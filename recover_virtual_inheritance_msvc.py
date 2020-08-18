import idc
import idascript
from idaapi import *

DWORD_SIZE = 8

def buildsegmap():
	segs = {}
	segs['code'] = []
	segs['wdata'] = []
	segs['rodata'] = []
	segs['got'] = []
	segs['plt'] = []
	segs['text'] = []
	segs['got_plt'] = []
	segs['extern'] = []

	for i in range(get_segm_qty()):
		seg = getnseg(i)
		sname = get_segm_name(seg)
		if seg.perm & SEGPERM_EXEC:
			if sname == ".plt":
				segs['plt'].append((sname, seg.startEA, seg.startEA + seg.size()))
			elif sname == ".text":
				segs['text'].append((sname, seg.startEA, seg.startEA + seg.size()))
			segs['code'].append((sname, seg.startEA, seg.startEA + seg.size()))

		elif seg.perm & SEGPERM_WRITE == 0 or sname == ".data.rel.ro" or sname == ".data.rel.ro.local":
			if sname == ".eh_frame" or sname == ".eh_frame_hdr": continue
			if sname == "extern":
				segs['extern'].append((sname, seg.startEA, seg.startEA + seg.size()))
			segs['rodata'].append((sname, seg.startEA, seg.startEA + seg.size()))

		elif seg.perm & SEGPERM_WRITE and not sname == ".data.rel.ro" and not sname == ".data.rel.ro.local":
			if sname == ".got.plt":
				segs['got_plt'].append((sname, seg.startEA, seg.startEA + seg.size()))
			elif sname == ".got":
				segs['got'].append((sname, seg.startEA, seg.startEA + seg.size()))
			segs['wdata'].append((sname, seg.startEA, seg.startEA + seg.size()))  
	return segs

def in_seg(val, segname, segs):
	if val == 0:
		return False
	for k,n,m in segs[segname]:
		if val >= n and val < m:
			return True
	return False



class VirtualInhAnalysis:

	def __init__(self, segs):
		self.segs = segs
		self.vbase_magics = [0, 0xffffff20, 0xffffffc0, 0xfffffe28, 0xfffffffc, 0xfffffff8]
		self.ctor_dtor = set()
		self.immediates_n_address = set()
		self.call_instrns = {}
		self.pure_virtual = 0
		self.vtables = {}
		self.func_to_vt = {}
		self.vbtables = {}
		self.func_that_initialize_vbtable = {}
		self.func_that_initialize_vbtable_addr = {}
		self.VBases = {}
		self.gatherImmediates()
		self.verifyVTables()
		self.identifyVirtualBases()

	def gatherImmediates(self):
		#global immediates_n_address, call_instrns
		potentials = set()

		for i in range(get_func_qty()):
			func = getn_func(i)
			#validFunctions.append(func.startEA)
			for ea in range(func.startEA, func.endEA):
				if "throw info for" in GetDisasm(ea) or "struct" in GetDisasm(ea):
					continue
				flags = get_flags_novalue(ea)
				if isHead(flags) and isCode(flags):
					if decode_insn(ea) == 0:
						continue
					# if func.startEA == 0x73D6C:
					# 	print format(func.startEA, 'x'), "got to immediates"
					for j in range(6):
						if cmd.Operands[j].type == o_imm and (cmd.itype == NN_mov or cmd.itype == NN_lea):
							imm_val = cmd.Operands[j].value
							if in_seg(imm_val, 'rodata', self.segs):
								potentials.add(imm_val)
								self.immediates_n_address.add((imm_val, ea, func.startEA))
						elif cmd.Operands[j].type == o_mem and (cmd.itype == NN_mov or cmd.itype == NN_lea):
							# if func.startEA == 0x73D6C:
							# 	print format(func.startEA, 'x'), "got to o_mem"
							imm_val = cmd.Operands[j].addr
							# if ea == 0xA0362:
							#     print "found2", in_seg(imm_val, 'got')
							if in_seg(imm_val, 'got', self.segs):
								imm_val = self.get_got_entry(imm_val)
							if in_seg(imm_val, 'rodata', self.segs):
								potentials.add(imm_val)
								self.immediates_n_address.add((imm_val, ea, func.startEA))
					if cmd.itype == NN_call or cmd.itype == NN_jmp:
						if not func.startEA in self.call_instrns:
							self.call_instrns[func.startEA] = []
						self.call_instrns[func.startEA].append((ea, cmd.Operands[0].addr))
			if func.tailqty > 0:
				fti = func_tail_iterator_t(func)
				ok = fti.first()
				while ok:
					ar = fti.chunk()
					for ea in range(ar.startEA, ar.endEA):
						if "throw info for" in GetDisasm(ea) or "struct" in GetDisasm(ea):
							continue
						flags = get_flags_novalue(ea)
						if isHead(flags) and isCode(flags):
							if decode_insn(ea) == 0:
								continue

							for j in range(6):
								if cmd.Operands[j].type == o_imm and (cmd.itype == NN_mov or cmd.itype == NN_lea):
									imm_val = cmd.Operands[j].value
									if in_seg(imm_val, 'rodata', self.segs):
										potentials.add(imm_val)
										self.immediates_n_address.add((imm_val, ea, func.startEA))
								elif cmd.Operands[j].type == o_mem and (cmd.itype == NN_mov or cmd.itype == NN_lea):
									imm_val = cmd.Operands[j].addr
									#if ea == 107972:
										#print format(imm_val,'x')
									if in_seg(imm_val, 'got', self.segs):
										imm_val = self.get_got_entry(imm_val)
									if in_seg(imm_val, 'rodata', self.segs):
										potentials.add(imm_val)
										self.immediates_n_address.add((imm_val, ea, func.startEA))
							if cmd.itype == NN_call or cmd.itype == NN_jmp:
								if not func.startEA in self.call_instrns:
									self.call_instrns[func.startEA] = []
								self.call_instrns[func.startEA].append((ea, cmd.Operands[0].addr))
					ok = fti.next()

		return potentials

	def get_got_entry(self, addr):
		for xref in XrefsFrom(addr, 0):
			ref_to = xref.to
			if in_seg(ref_to, 'rodata', self.segs):
				#print format(ref_to, 'x')
				#return ref_to + (DWORD_SIZE * 2)
				return ref_to
		return 0

	def pure_v(self, addr):
		#global pure_virtual
		if get_func_name(addr) == "_purecall":
			if self.pure_virtual == 0:
				self.pure_virtual = addr
			return True
		else:
			decode_insn(addr)
			next_addr = cmd.Operands[0].addr
			if in_seg(next_addr, 'got_plt', self.segs):
				if get_func_name(self.get_dword(next_addr)) == "_purecall":
					if self.pure_virtual == 0:
						self.pure_virtual = addr
					return True
			return False

	def is_abst_class(self, pv):
		while True:
			if (self.get_dword(pv) == 0 and self.get_dword(pv + DWORD_SIZE) == 0):
				return True
			elif in_seg(self.get_dword(pv), 'code', self.segs) or self.pure_v(self.get_dword(pv)):
				pv = pv + DWORD_SIZE
			else:
				return False

	def get_dword(self, ea):
		if ea <= 0xffffffff:
			return Dword(ea)
		else:
			return Qword(ea)


	def verifyVTables(self):
		# global vtables
		# global segs
		# global vfns
		# global immediates_n_address
		# global ctor_dtor
		# imm_val = 0
		# print "got to verifyVTables"
		# buildsegmap()
		# immediates = gatherImmediates()
		#print "Immediates: ", ["0x%x" % x for x in immediates]

		for (pv, ea, func) in self.immediates_n_address:
			#print format(pv, 'x'), format(ea, 'x'), format(func, 'x')
			if func == 0x140006DA0:
				print format(pv, 'x'), format(ea, 'x'), format(func, 'x')
			self.verifyAVtable(pv, ea, func)
			self.verifyAVBTable(pv, ea, func)

		# for v in vtables.keys():
		# 	for f in vtables[v]['vfptrs']:
		# 		f_ptr = get_func(f)
		# 		if not f_ptr is None:
		# 			if get_func(f).startEA == f:
		# 				vfns[f] = True
		return


	def verifyAVtable(self, pv, ea, func):
		#global vtables, sec_vptrs_to_address, has_vir_dtor, vptr_to_top_of_vtable

		# if pv == pure_virtual:
		# 	return False

		entry = self.get_dword(pv)
		# if func == 0x140026980:
		# 	print format(entry, 'x'), in_seg(entry, 'code'), pure_v(entry), in_seg(get_dword(pv - DWORD_SIZE), 'rodata'), get_dword(pv - DWORD_SIZE) == 0
		if not ((in_seg(entry, 'code', self.segs) or self.pure_v(entry)) and (in_seg(self.get_dword(pv - DWORD_SIZE), 'rodata', self.segs) or  self.get_dword(pv - DWORD_SIZE) == 0)):
			return False #meaning address not a vtable


		# We have a vtable
		self.ctor_dtor.add(func)
		if not func in self.func_to_vt:
			self.func_to_vt[func] = set()
		self.func_to_vt[func].add(pv)
		#print format(func, 'x'), format(pv, 'x')
		vtable = {}
		if (self.is_abst_class(pv)):
			vtable['abst'] = True
		else:
			vtable['abst'] = False
		vtable['address'] = pv
		vtable['vfptrs'] = []
		vtable['vfptrs'].append(entry)

		curr = 1
		while True:
			entry = self.get_dword(pv + curr * DWORD_SIZE)
			# if pv == 0x46e7d0:
			#     print format(pv + curr * DWORD_SIZE, 'x')
			curr += 1
			if not ((in_seg(entry, 'code', self.segs) or self.pure_v(entry)) and (in_seg(self.get_dword(pv - DWORD_SIZE), 'rodata', self.segs) or  self.get_dword(pv - DWORD_SIZE) == 0)): break
			vtable['vfptrs'].append(entry)

		self.vtables[pv] = vtable


	def verifyAVBTable(self, imm, ea, func):
		#global vbtables
		#if get_dword(imm) != 0xfffffffc: return # this looks like a signature for VBTables, just an assumption for now
		#take "0xffffffa8" as input, it determines the offset added to rcx before calling virtual base
		#offset_added = vbaseoffset+(0xffffffff-0xffffffa8)+1
		# if (Dword(imm) != vbase_base 
		# 	and Dword(imm) != 0 
		# 	and Dword(imm) != vbase_base2 
		# 	and Dword(imm) != vbase_base3 
		# 	and Dword(imm) != vbase_base4
		# 	and Dword(imm) != vbase_base5
		# 	and Dword(imm) != vbase_base6): return
		found = False
		for i in self.vbase_magics:
			if Dword(imm) == i:
				found = True
				break
		if not found: return

		# if func == 0x140007E30:
		# 	print "got here 1"
		entries = []
		vals = imm + 4
		while True:
			if Dword(vals) >= 0 and Dword(vals) < 0x4096: 
				entries.append(Dword(vals))
				vals += 4
			else:
				break
		if func == 0x140006DA0:
			print len(entries)
		if len(entries) > 0:
			self.vbtables[imm] = entries
			if not func in self.func_that_initialize_vbtable:
				self.func_that_initialize_vbtable[func] = set()
				self.func_that_initialize_vbtable_addr[func] = set()
			self.func_that_initialize_vbtable[func].add(imm)
			self.func_that_initialize_vbtable_addr[func].add(ea)

	def getAddedOffset(self, addr):
		i = 0
		while i <= 15:
			decode_insn(addr)
			#if cmd.itype == 6 and cmd.Operands[0].reg == 1 and cmd.Operands[1].type == o_imm: #sink is ecx
			if cmd.itype == 6 and cmd.Operands[1].type == o_imm: #sink is ecx
				return cmd.Operands[1].value
			addr = PrevHead(addr)
			i += 1
			#else:
		return -1

	def getMovAddedOffset(self, addr):
		decode_insn(addr)
		if cmd.itype == 122 and cmd.Operands[0].type == 4 and cmd.Operands[1].type == o_reg:
			return cmd.Operands[0].addr
		return -1

	def processInlinedCtorsDtors(self, addr):
		init_addr = addr
		decode_insn(addr)
		sink = cmd.Operands[0].reg #get rax in 1 above
		i = 0
		x = -1
		while i < 5: #try to find instn 2 above
			addr = NextHead(addr)
			decode_insn(addr)
			#reg 0 = rcx
			if init_addr == 0x14072490D:
				print cmd.Operands[0].type, o_displ, cmd.Operands[1].reg, sink, cmd.Operands[0].reg, format(cmd.Operands[0].addr, 'x')
			if (cmd.Operands[0].type == o_displ or cmd.Operands[0].type == o_phrase) and cmd.Operands[1].reg == sink:
				x = cmd.Operands[0].addr
				break
			i += 1
		if init_addr == 0x14072490D:
			print "x is ", format(x, 'x') 
		if x == -1 : return -1
		i = 0
		vptr = -1
		while i < 10: #try to get instn 3 above
			addr = NextHead(addr)
			decode_insn(addr)
			# if init_addr == 0x140640DE2:
			# 	print cmd.Operands[0].type, o_reg, cmd.Operands[1].type, o_mem, format(cmd.Operands[1].value, 'x'), cmd.Operands[1].value in vtables 
			if cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_imm and cmd.Operands[1].value in vtables:
				vptr = cmd.Operands[1].value
				sink = cmd.Operands[0].reg
				break
			if cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_mem and cmd.Operands[1].addr in vtables:
				vptr = cmd.Operands[1].addr
				sink = cmd.Operands[0].reg
				break
			i += 1
		if init_addr == 0x14072490D:
			print "vptr is ", format(vptr, 'x')
		if vptr == -1: return -1
		i = 0
		v = -1
		while i < 5: #try to get instn 4 above
			addr = NextHead(addr)
			decode_insn(addr)
			if cmd.Operands[0].type == o_displ and cmd.Operands[1].type == o_reg and cmd.Operands[1].reg == sink:
				v = cmd.Operands[0].addr
				break
			i += 1
		if init_addr == 0x14072490D:
			print "v is ", format(v, 'x')
		if v == -1: return -1
		return (v-x, vptr)



	def identifyVirtualBases(self):
		#global ctor_dtor, func_that_initialize_vbtable, func_that_initialize_vbtable_addr, call_instrns
		for c in self.ctor_dtor:
			if c in self.func_that_initialize_vbtable:
				vbtables_initialized = sorted(self.func_that_initialize_vbtable[c])
				vbtables_initialized_addr = sorted(self.func_that_initialize_vbtable_addr[c])
				if c in self.call_instrns:
					for (ea, target) in self.call_instrns[c]:
						offset_added = self.getAddedOffset(PrevHead(ea))
						if offset_added != -1:
							mov_offset_added = self.getMovAddedOffset(NextHead(vbtables_initialized_addr[0]))
		
							found = False
							for i in self.vbase_magics:
								if i == 0 and offset_added in self.vbtables[vbtables_initialized[0]]:
									found = True
									break
								elif offset_added - (0xffffffff-i+1) in self.vbtables[vbtables_initialized[0]]:
									found = True
									break
							if found:
								if not c in self.VBases:
									self.VBases[c] = []

								self.VBases[c].append(vbtables_initialized_addr[0])

				ret = self.processInlinedCtorsDtors(vbtables_initialized_addr[0])
				if ret != -1:
					#print format(offset, 'x'), format(vptr, 'x'), format(vbtables_initialized_addr[0], 'x')
					if ret[0] in self.vbtables[vbtables_initialized[0]]:
						if not c in self.VBases:
							self.VBases[c] = []

						self.VBases[c].append(vbtables_initialized_addr[0])

def main():

	vt_inh = VirtualInhAnalysis(buildsegmap())
	print "VBTables"
	for v in vt_inh.vbtables:
		print format(v, 'x')

	print "Ctor/Dtor of Derived [Ctor/Dtor of Virtual Bases]"
	len1 = 0
	leng1 = 0
	for vb in vt_inh.VBases:
		if len(vt_inh.VBases[vb]) == 1:
			len1 += 1
		elif len(vt_inh.VBases[vb]) > 1:
			leng1 += 1
		print format(vb, 'x'), [format(x, 'x') for x in vt_inh.VBases[vb]]
	print "# classes with one or more Virtual Bases: ",len(vt_inh.VBases)
	print "# classes with Virtual Bases = 1: ", len1
	print "# classes with Virtual Bases: ", leng1
	print "# of VTables: ", len(vt_inh.vtables)

if __name__ == "__main__":
	main()