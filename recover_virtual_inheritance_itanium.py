import idc
import idascript
from idaapi import *
import copy

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
	#global segs
	if val == 0:
		return False
	for k,n,m in segs[segname]:
		if val >= n and val < m:
			return True
	return False

def get_got_entry(addr):
	return Dword(addr)

class VTablesAnalysis:
	"""Class recovers VTables from the binary."""
	def __init__(self, segs):
		self.segs = segs
		self.pure_virtual = 0
		self.vtables = {}
		self.validFunctions = []
		self.vfns = {}
		self.sec_vptrs_to_address = {}
		self.has_vir_dtor = []
		self.vptr_to_top_of_vtable = {}
		self.top_of_vtable_tovptr = {}
		self.gatherImmediates()
		self.verifyVTables()

	def is_abst_class(self, pv):
		while True:
			if (Dword(pv) == 0 and Dword(pv + DWORD_SIZE) == 0):
				return True
			elif in_seg(Dword(pv), 'code', self.segs) or self.pure_v(Dword(pv)):
				pv = pv + DWORD_SIZE
			else:
				return False

	def pure_v(self, addr):
		#global pure_virtual
		if addr == 0x0: return True
		if get_func_name(addr) == "__cxa_pure_virtual":
			if self.pure_virtual == 0:
				self.pure_virtual = addr
			return True
		else:
			decode_insn(addr)
			next_addr = cmd.Operands[0].addr
			if in_seg(next_addr, 'got_plt', self.segs):
				if get_func_name(Dword(next_addr)) == "__cxa_pure_virtual":
					if self.pure_virtual == 0:
						self.pure_virtual = addr
					return True
			return False

	def gatherImmediates(self):
		#global immediates_n_address
		self.potentials = set() #consider removing
		self.immediates_n_address = []
		for i in range(get_func_qty()):
			func = getn_func(i)
			self.validFunctions.append(func.startEA)
			for ea in range(func.startEA, func.endEA):
				flags = get_flags_novalue(ea)
				if isHead(flags) and isCode(flags):
					if decode_insn(ea) == 0:
						continue
					for j in range(6):
						if cmd.Operands[j].type == o_imm:
							imm_val = cmd.Operands[j].value
							if in_seg(imm_val, 'rodata', self.segs):
								self.potentials.add(imm_val)
								self.immediates_n_address.append((imm_val, 'd', ea))
						elif cmd.Operands[j].type == o_mem:
							imm_val = cmd.Operands[j].addr
							if in_seg(imm_val, 'rodata', self.segs):
								self.potentials.add(imm_val)
								self.immediates_n_address.append((imm_val, 'd', ea))
							elif in_seg(imm_val, 'got', self.segs):
								self.potentials.add(imm_val)
								self.immediates_n_address.append((imm_val, 'i', ea))

			if func.tailqty > 0:
				fti = func_tail_iterator_t(func)
				ok = fti.first()
				while ok:
					ar = fti.chunk()
					for ea in range(ar.startEA, ar.endEA):
						flags = get_flags_novalue(ea)
						if isHead(flags) and isCode(flags):
							if decode_insn(ea) == 0:
								continue

							for j in range(6):
								if cmd.Operands[j].type == o_imm:
									imm_val = cmd.Operands[j].value
									if in_seg(imm_val, 'rodata', self.segs):
										self.potentials.add(imm_val)
										self.immediates_n_address.append((imm_val, 'd', ea))
								elif cmd.Operands[j].type == o_mem:
									imm_val = cmd.Operands[j].addr
									if in_seg(imm_val, 'rodata', self.segs):
										self.potentials.add(imm_val)
										self.immediates_n_address.append((imm_val, 'd', ea))
									elif in_seg(imm_val, 'got', self.segs):
										self.potentials.add(imm_val)
										self.immediates_n_address.append((imm_val, 'i', ea))

					ok = fti.next()

		#return potentials

	def get_vptr_from_top_address(self, ea):
		i = 0
		decode_insn(ea)
		init_ea = ea
		sink_reg = cmd.Operands[0].reg
		while i < 10:
			ea = NextHead(ea)
			decode_insn(ea)
			if cmd.Operands[1].type == o_reg and sink_reg == cmd.Operands[1].reg and (cmd.itype in {NN_lea, cmd.itype}) and (cmd.Operands[0].type in {o_phrase, o_displ}) and (cmd.Operands[0].reg in {3, 7}):
				return False
			if sink_reg == cmd.Operands[1].reg and cmd.itype == NN_lea and cmd.Operands[1].type == o_displ and not cmd.Operands[1].addr > 0x0fffffffffffffff: #that will be negative
				return cmd.Operands[1].addr
			if sink_reg == cmd.Operands[1].reg and cmd.itype == NN_add and cmd.Operands[1].type == o_imm and not cmd.Operands[1].value > 0x0fffffffffffffff:
				return cmd.Operands[1].value
			i += 1
		return False

	def is_top_of_vtable(self, v, ea):
		poss_offset_added = self.get_vptr_from_top_address(ea)
		if not poss_offset_added == False:
			new_addr = v + poss_offset_added
			if in_seg(Dword(new_addr), 'text', self.segs) or self.pure_v(Dword(new_addr)) or in_seg(Dword(new_addr-DWORD_SIZE), 'rodata', self.segs):
				return (True, new_addr)
		if not type(Dword(v + DWORD_SIZE)) in {int, long} :
			return (False, 0)
		if ((Dword(v - DWORD_SIZE) == 0 or in_seg(Dword(v - DWORD_SIZE), 'rodata', self.segs)) and Dword(v - DWORD_SIZE*2) == 0 and 
				((get_func_name(Dword(v)) == "__cxa_pure_virtual") or in_seg(Dword(v), 'code', self.segs))):
			return (False, 0)
		if ( (not in_seg(Dword(v - DWORD_SIZE), 'rodata', self.segs) or get_func_name(Dword(v - DWORD_SIZE)) == "__cxa_pure_virtual" or 
				(in_seg(Dword(v - DWORD_SIZE), 'rodata', self.segs) and not get_func_name(Dword(v + DWORD_SIZE)) == "__cxa_pure_virtual") and not in_seg(Dword(v + DWORD_SIZE), 'code', self.segs)) and
				(in_seg(Dword(v + DWORD_SIZE), 'rodata', self.segs) or Dword(v + DWORD_SIZE) == 0) ):
			return (True, v)
		else:
			return (False, 0)

	def verifyAVtable(self, pv, typ='n', ea=-1):
		#global vtables, sec_vptrs_to_address, has_vir_dtor, vptr_to_top_of_vtable, top_of_vtable_tovptr
		if self.pure_virtual != 0 and (pv == self.pure_virtual or Dword(pv) == self.pure_virtual):
			return False
		if pv in self.vtables or Dword(pv) in self.vtables:
			if ea == -1 or (pv in self.top_of_vtable_tovptr and (self.top_of_vtable_tovptr[pv] - pv) < self.get_vptr_from_top_address(ea)) or ((Dword(pv) in self.top_of_vtable_tovptr and (self.top_of_vtable_tovptr[Dword(pv)] - Dword(pv)) < self.get_vptr_from_top_address(ea))):
				return True
		if pv in self.vptr_to_top_of_vtable or Dword(pv) in self.vptr_to_top_of_vtable:
			return True
		real_pv = pv
		f = pv
		if ea != -1:
			if typ == 'i':
				p_vtp = get_got_entry(pv)
				if p_vtp == 0:
					return False
				else:
					real_pv = p_vtp
					offset_actual_vptr_possibly = self.get_vptr_from_top_address(ea)
					if not offset_actual_vptr_possibly == False:
						pv = p_vtp + offset_actual_vptr_possibly
					else:
						pv = p_vtp + (DWORD_SIZE * 2)
			else:
			    (is_top, new_addr) = self.is_top_of_vtable(pv, ea);
			    if is_top:
			        pv = new_addr
		entry = Dword(pv)
		typeinfoptr = Dword(pv - DWORD_SIZE)
		if (not in_seg(typeinfoptr, 'rodata', self.segs)) and (entry != 0 or Dword(pv + DWORD_SIZE) != 0 or (not in_seg(Dword(pv + (DWORD_SIZE *2)), 'code', self.segs) and not self.pure_v(Dword(pv + (DWORD_SIZE *2))) and not self.pure_v(Dword(pv)))) and (not in_seg(entry, 'code', self.segs) and not self.pure_v(Dword(pv + (DWORD_SIZE *2))) and not self.pure_v(Dword(pv))):
		    return False #meaning address not a vtable

		if (typeinfoptr != 0) and (not in_seg(typeinfoptr, 'rodata', self.segs)): return False #meaning address not a vtable
		vtable = {}
		if (self.is_abst_class(pv)):
		    vtable['abst'] = True
		else:
		    vtable['abst'] = False
		vtable['address'] = pv
		vtable['vfptrs'] = []
		vtable['secondaries'] = []

		vtable['vfptrs'].append(entry)

		if (entry == 0 and Dword(pv + DWORD_SIZE) == 0):
		    self.has_vir_dtor.append(pv)
		    curr = 3
		else:
		    curr = 1
		zero_entries = 0
		while True:
		    entry = Dword(pv + curr * DWORD_SIZE)
		    curr += 1
		    if (in_seg(entry, 'code', self.segs) and entry in self.validFunctions) or self.pure_v(entry) or in_seg(entry, 'extern', self.segs):
		        if zero_entries == 1:
		            break
		        vtable['vfptrs'].append(entry)
		        if zero_entries == 2:
		            vtable['vfptrs'].append(entry)
		            vtable['vfptrs'].append(entry)

		    elif entry == 0 and zero_entries <2:
		        zero_entries += 1
		    else:
		        break

		vtable['typeinfo'] = Dword(pv - DWORD_SIZE)
		vtable['offsetToTop'] = Dword(pv - 2*DWORD_SIZE)
		if not(real_pv == pv):
		    vtable['dif'] = 1
		    vtable['cal_pv'] = pv
		else:
		    vtable['dif'] = 0

		if vtable['offsetToTop'] != 0 and real_pv in self.vtables:
		    if not ea == -1:
		        self.sec_vptrs_to_address[ea] = pv
		    self.vtables[pv] = vtable
		else:
		    self.vtables[real_pv] = vtable
		if ea != -1 and real_pv in self.vtables: #only do this if vptr gotten from text section, not from VTT
		    if pv in self.vptr_to_top_of_vtable:
		        del self.top_of_vtable_tovptr[self.vptr_to_top_of_vtable[pv]]
		    if real_pv in self.top_of_vtable_tovptr:
		        del self.vptr_to_top_of_vtable[self.top_of_vtable_tovptr[real_pv]]
		    self.vptr_to_top_of_vtable[pv] = real_pv
		    self.top_of_vtable_tovptr[real_pv] = pv
		return True #meaning that the address is indeed a vtables

	def verifyVTables(self):
	    #global vtables
	    #global segs
	    #global vfns
	    #global sec_vptrs_to_address, has_vir_dtor, vptr_to_top_of_vtable, top_of_vtable_tovptr
	    #global all_immediates
	    #global immediates_n_address
	    #imm_val = 0

	    for (pv, typ, ea) in self.immediates_n_address:
	        self.verifyAVtable(pv, typ, ea)
	    self.remove_VTTs_identified_as_VTables()
	    return

	def remove_VTTs_identified_as_VTables(self):
	    #global vtables, vfns
	    for v in self.vtables.keys():
	        for f in self.vtables[v]['vfptrs']:
	            if f in self.vtables and not in_seg(f, "extern", self.segs):
	                del self.vtables[v]
	                break
	            f_ptr = get_func(f)
	            if not f_ptr is None:
	                if get_func(f).startEA == f:
	                    self.vfns[f] = True


class CtorDtorAnalysis:
	"""Class recovers constructors and destructors from a binary."""
	def __init__(self, segs, vtables, top_of_vtable_tovptr, subVTTKeys):
		self.segs = segs
		self.vtables = vtables
		self.top_of_vtable_tovptr = top_of_vtable_tovptr
		self.ctor_dtor_vt = {}
		self.func_vt = {}
		self.call_instns = {}
		self.list_of_ctor_dtors = []
		self.VTT_addr_write_instns = {}
		self.ctor_dtors = {}
		self.parsedInstns = {} 
		self.firstVTTWrites = {} 
		self.vptr_writes = {} 
		self.identify_ctor_dtor()
		self.parseFuncs(subVTTKeys)
		self.assign_vptr_to_ctor_dtor()

	def identify_ctor_dtor(self):
	    #global vtables, ctor_dtor_vt, list_of_ctor_dtors, VTT_addr_write_instns, ctor_dtors, func_vt, call_instns
	    
	    for i in range(get_func_qty()):
	        no_oimm = 0
	        func = getn_func(i)
	        insn_count = 0
	        for ea in range(func.startEA, func.endEA):
	            flags = get_flags_novalue(ea)
	            if isHead(flags) and isCode(flags):
	                if decode_insn(ea) == 0:
	                    continue
	                for j in range(5):          
	                    if cmd.Operands[j].type == o_imm:
	                        if cmd.Operands[j].value in self.vtables or cmd.Operands[j].value in self.top_of_vtable_tovptr:
	                            if cmd.Operands[j].value in self.vtables:
	                                vta = cmd.Operands[j].value
	                            else:
	                                vta = self.top_of_vtable_tovptr[cmd.Operands[j].value]
	                            if not func.startEA in self.ctor_dtors:
	                                self.ctor_dtors[func.startEA] = []
	                            self.ctor_dtors[func.startEA].append(vta)
	                            self.list_of_ctor_dtors.append((func.startEA, func.endEA))
	                        


	                    if cmd.Operands[j].type == o_mem:
	                        ptr = cmd.Operands[j].addr
	                        if in_seg(ptr, 'got', self.segs):
	                            ptr = get_got_entry(ptr)
	                        if ptr in self.vtables or ptr in self.top_of_vtable_tovptr:
	                            if ptr in self.vtables:
	                                pass
	                            else:
	                                ptr = self.top_of_vtable_tovptr[ptr]
	                            if not func.startEA in self.ctor_dtors:
	                                self.ctor_dtors[func.startEA] = []
	                            self.ctor_dtors[func.startEA].append(ptr)
	                            self.list_of_ctor_dtors.append((func.startEA, func.endEA))
	                        
	                
	                if cmd.itype == NN_call or cmd.itype == NN_jmp:
	                    if not func.startEA in self.call_instns:
	                        self.call_instns[func.startEA] = []
	                    self.call_instns[func.startEA].append((ea, cmd.Operands[0].addr))  

	        if func.tailqty > 0:
	            fti = func_tail_iterator_t(func)
	            ok = fti.first()

	            while ok:
	                ar = fti.chunk()

	                for ea in range(ar.startEA, ar.endEA):
	                    flags = get_flags_novalue(ea)
	                    if isHead(flags) and isCode(flags):
	                        if decode_insn(ea) == 0:
	                            continue

	                        for j in range(5):
	                            if cmd.Operands[j].type == o_imm:
	                                if cmd.Operands[j].value in self.vtables or cmd.Operands[j].value in self.top_of_vtable_tovptr:
	                                    if cmd.Operands[j].value in self.vtables:
	                                        vta = cmd.Operands[j].value
	                                    else:
	                                        vta = self.top_of_vtable_tovptr[cmd.Operands[j].value]
	                                    if not func.startEA in self.ctor_dtors:
	                                        self.ctor_dtors[func.startEA] = []
	                                    self.ctor_dtors[func.startEA].append(vta)
	                                    self.list_of_ctor_dtors.append((func.startEA, func.endEA))
	                                

	                            if cmd.Operands[j].type == o_mem:
	                                ptr = cmd.Operands[j].addr
	                                if in_seg(ptr, 'got', self.segs):
	                                    ptr = get_got_entry(ptr)
	                                if ptr in self.vtables or ptr in self.top_of_vtable_tovptr:
	                                    if ptr in self.vtables:
	                                        pass
	                                    else:
	                                        ptr = self.top_of_vtable_tovptr[ptr]
	                                    if not func.startEA in self.ctor_dtors:
	                                        self.ctor_dtors[func.startEA] = []
	                                    self.ctor_dtors[func.startEA].append(ptr)
	                                    self.list_of_ctor_dtors.append((func.startEA, func.endEA))
	                                

	                        if cmd.itype == NN_call or cmd.itype == NN_jmp:
	                            if not func.startEA in self.call_instns:
	                                self.call_instns[func.startEA] = []
	                            self.call_instns[func.startEA].append((ea, cmd.Operands[0].addr))
	                ok = fti.next()

	def assign_vptr_to_ctor_dtor(self):
	    #global ctor_dtors, ctor_dtor_vt, func_vt, vptr_writes

	    for f,v in self.ctor_dtors.items():
	        is_set = 0
	        if f in self.vptr_writes:
	            ea = 0
	            owner_vptr = -1
	            for vp in self.vptr_writes[f]:
	                if self.vptr_writes[f][vp]['addr'] > ea and self.vptr_writes[f][vp]['offset'] == 0:
	                    ea = vptr_writes[f][vp]['addr']
	                    owner_vptr = vp
	            if owner_vptr != -1 and owner_vptr in self.vtables and self.vtables[owner_vptr]['offsetToTop'] == 0:
	                if not owner_vptr in self.ctor_dtor_vt:
	                    self.ctor_dtor_vt[owner_vptr] = []
	                self.ctor_dtor_vt[owner_vptr].append(f)
	                self.func_vt[f] = owner_vptr
	                is_set = 1
	        if is_set == 0:   
	            for k in v:
	                if not k in self.vtables:
	                    continue
	                if self.vtables[k]['offsetToTop'] == 0: # This is the complete obj!
	                    if not k in self.ctor_dtor_vt:
	                        self.ctor_dtor_vt[k] = []
	                    self.ctor_dtor_vt[k].append(f)
	                    self.func_vt[f] = k
	                    break

	def add_remove_elem(self, objAddrs, reg1, reg2):
	    for off in objAddrs:
	        if reg1 in objAddrs[off]:
	            objAddrs[off].remove(reg1)
	            break
	    for off in objAddrs:
	        if reg2 in objAddrs[off]:
	            objAddrs[off].append(reg1)
	            break
	    return objAddrs

	def create_new_offset_entry(self, objAddrs, offset, reg1):
	    for off in objAddrs:
	        if reg1 in objAddrs[off]:
	            if offset in objAddrs:
	                objAddrs[offset].append(reg1)
	            else:
	                objAddrs[offset] = []
	                objAddrs[offset].append(reg1)
	            objAddrs[off].remove(reg1)
	            break
	    return objAddrs

	def parseFuncs(self, subVTTKeys):
		"""Function helps to know the offset within an object that is stored in rdi before making a ctor or dtor call"""
		#global parsedInstns, VTT_addr_write_instns, list_of_ctor_dtors, firstVTTWrites, vptr_writes, subVTTKeys
		for (s, e) in self.list_of_ctor_dtors:
		    reg_with_vtt_address = -1
		    current_vtt_address = -1 
		    reg_vptr_write_moves = {}
		    current_obj_addr = set()
		    current_obj_addr.add(7)
		    objAddrs = {}
		    objAddrs[0] = []
		    objAddrs[0].append(7)
		    self.vptr_writes[s] = {}
		    for ea in range(s, e):
		        flags = get_flags_novalue(ea)
		        if decode_insn(ea) == 0 or not isCode(flags):
		            continue
		        if cmd.itype in {88, NN_call, NN_jmp}  and "__Znwm" in GetDisasm(ea):
		            objAddrs[0].append(0)
		            current_obj_addr.add(0)
		            continue
		        if cmd.Operands[1].type == o_mem:
		            if cmd.Operands[0].reg in current_obj_addr:
		                current_obj_addr.remove(cmd.Operands[0].reg)
		            if in_seg(cmd.Operands[1].addr, 'got', self.segs):
		                imm_addr = Dword(cmd.Operands[1].addr)
		            else:
		                imm_addr = cmd.Operands[1].addr
		            if imm_addr in subVTTKeys:
		                current_vtt_address = imm_addr
		                reg_with_vtt_address = cmd.Operands[0].reg
		                if cmd.Operands[0].reg == 6:
		                    if not s in self.VTT_addr_write_instns:
		                        self.VTT_addr_write_instns[s] = set()
		                        self.firstVTTWrites[s] = ea 
		                    self.VTT_addr_write_instns[s].add(current_vtt_address)
		                    current_vtt_address = -1 
		                continue
		            if imm_addr in self.vtables and not imm_addr in self.vptr_writes[s]:
		                vptr = imm_addr
		                self.vptr_writes[s][vptr] = {}
		                self.vptr_writes[s][vptr]['addr'] = ea
		                self.vptr_writes[s][vptr]['offset'] = -1
		                reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
		                continue
		            if imm_addr in self.top_of_vtable_tovptr and not imm_addr in self.vptr_writes[s]:
		                vptr = self.top_of_vtable_tovptr[imm_addr]
		                self.vptr_writes[s][vptr] = {}
		                self.vptr_writes[s][vptr]['addr'] = ea
		                self.vptr_writes[s][vptr]['offset'] = -1
		                reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
		                continue
		        elif cmd.Operands[1].type == o_imm:
		            if cmd.Operands[0].reg in current_obj_addr:
		                current_obj_addr.remove(cmd.Operands[0].reg)
		            if cmd.Operands[1].value in subVTTKeys:
		                current_vtt_address = cmd.Operands[1].value
		                reg_with_vtt_address = cmd.Operands[0].reg
		                if cmd.Operands[0].reg == 6:
		                    if not s in self.VTT_addr_write_instns:
		                        self.VTT_addr_write_instns[s] = set()
		                        self.firstVTTWrites[s] = ea
		                    self.VTT_addr_write_instns[s].add(current_vtt_address)
		                    current_vtt_address = -1
		                continue
		            if cmd.Operands[1].value in self.vtables and not cmd.Operands[1].value in self.vptr_writes:
		                vptr = cmd.Operands[1].value
		                self.vptr_writes[s][vptr] = {}
		                self.vptr_writes[s][vptr]['addr'] = ea
		                self.vptr_writes[s][vptr]['offset'] = -1
		                reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
		                continue
		            if cmd.Operands[1].value in self.top_of_vtable_tovptr and not self.top_of_vtable_tovptr[cmd.Operands[1].value] in self.vptr_writes:
		                vptr = self.top_of_vtable_tovptr[cmd.Operands[1].value]
		                self.vptr_writes[s][vptr]={}
		                self.vptr_writes[s][vptr]['addr'] = ea
		                self.vptr_writes[s][vptr]['offset'] = -1
		                reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
		                continue
		        if cmd.itype in {NN_lea, NN_mov} and cmd.Operands[1].reg in current_obj_addr and cmd.Operands[1].type == o_reg:
		            current_obj_addr.add(cmd.Operands[0].reg)
		        elif cmd.Operands[0].type == o_reg and cmd.Operands[0].reg in current_obj_addr and cmd.Operands[0].type in {o_reg, o_phrase, o_displ} and cmd.itype in {NN_lea, NN_mov}:
		            current_obj_addr.remove(cmd.Operands[0].reg)
		        elif current_vtt_address != -1 and cmd.Operands[0].reg == 6 and cmd.Operands[1].reg == reg_with_vtt_address:
		            vtt_offset = 0
		            if cmd.Operands[1].type == o_displ and cmd.itype in {NN_lea, NN_mov}:
		                vtt_offset = cmd.Operands[1].addr
		            if not s in self.VTT_addr_write_instns:
		                self.VTT_addr_write_instns[s] = set()
		                self.firstVTTWrites[s] = ea
		            self.VTT_addr_write_instns[s].add(current_vtt_address + vtt_offset)
		            current_vtt_address = -1

		        elif cmd.Operands[0].reg in reg_vptr_write_moves and cmd.itype in {NN_lea, NN_mov} and cmd.Operands[0].type == o_reg:
		            del reg_vptr_write_moves[cmd.Operands[0].reg]
		        elif cmd.Operands[1].reg in reg_vptr_write_moves and cmd.itype in {NN_lea, NN_mov}:
		            if cmd.Operands[0].type == o_reg:
		                reg_vptr_write_moves[cmd.Operands[0].reg] = reg_vptr_write_moves[cmd.Operands[1].reg]
		            elif cmd.Operands[0].type == o_phrase and cmd.Operands[0].reg in current_obj_addr and cmd.Operands[1].type == o_reg: #mov [rdi], reg
		                vptr = reg_vptr_write_moves[cmd.Operands[1].reg]
		                if vptr in self.vptr_writes[s]:
		                    self.vptr_writes[s][vptr]['offset'] = 0
		                    self.vptr_writes[s][vptr]['addr'] = ea
		                    del reg_vptr_write_moves[cmd.Operands[1].reg]
		            elif cmd.Operands[0].type == o_displ and cmd.Operands[0].reg in current_obj_addr and cmd.Operands[1].type == o_reg: #mov [rdi+x], reg
		                vptr = reg_vptr_write_moves[cmd.Operands[1].reg]
		                if vptr in self.vptr_writes[s] and (self.vptr_writes[s][vptr]['offset'] != 0 or cmd.Operands[0].addr == 0):
		                    self.vptr_writes[s][vptr]['offset'] = cmd.Operands[0].addr
		                    self.vptr_writes[s][vptr]['addr'] = ea
		                    del reg_vptr_write_moves[cmd.Operands[1].reg]
		        if cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_reg and cmd.itype == NN_mov:
		            reg1 = cmd.Operands[0].reg 
		            reg2 = cmd.Operands[1].reg
		            objAddrs = self.add_remove_elem(objAddrs, reg1, reg2)

		        elif cmd.Operands[0].type == o_displ and cmd.Operands[1].type == o_reg and cmd.itype == NN_mov :
		            offset = cmd.Operands[0].addr
		            reg1 = str(cmd.Operands[0].reg)+"+"+str(offset)#
		            reg2 = cmd.Operands[1].reg
		            objAddrs = self.add_remove_elem(objAddrs, reg1, reg2)

		        elif cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_displ and cmd.itype == NN_mov:
		            reg1 = cmd.Operands[0].reg
		            offset = cmd.Operands[1].addr
		            reg2 = str(cmd.Operands[1].reg)+"+"+str(offset)
		            objAddrs = self.add_remove_elem(objAddrs, reg1, reg2)

		        elif cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_displ and cmd.itype == NN_lea:
		            reg1 = cmd.Operands[0].reg
		            offset = cmd.Operands[1].addr
		            reg2 = cmd.Operands[1].reg
		            if current_vtt_address != -1 and reg2 == reg_with_vtt_address:
		                current_vtt_address += offset
		                continue
		            objAddrs = self.create_new_offset_entry(objAddrs, offset, reg2)
		            objAddrs = self.add_remove_elem(objAddrs, reg1, reg2)

		        elif (cmd.Operands[0].type == o_reg or cmd.Operands[0].type == o_displ) and (cmd.Operands[1].type == o_imm or cmd.Operands[1].type == o_mem) and cmd.itype == NN_lea:
		            reg1 = cmd.Operands[0].reg
		            for off in objAddrs:
		                if  reg1 in objAddrs[off]:
		                    objAddrs[off].remove(reg1)
		                    break
		        elif cmd.Operands[0].type == o_reg and cmd.itype == NN_add:
		            reg1 = cmd.Operands[0].reg
		            offset = cmd.Operands[1].value
		            objAddrs = self.create_new_offset_entry(objAddrs, offset, reg1)
		        self.parsedInstns[ea] = copy.deepcopy(objAddrs)

class VirtualInheritanceAnalysis:

	def __init__(self, segs, vt_obj):
		self.segs = segs
		self.vt_obj = vt_obj
		self.VTTs = {}
		self.VTTEntrys_To_Vtables = {}
		self.possible_VTT_Entries = []
		self.subVTTs = {}
		self.subVTTKeys = []
		self.possible_constructorVTables = set()
		self.VTables_To_VTTEntries = {}
		self.vbaseOffsets = {}
		self.distinctVBases = {}
		self.intermediate_bases = {}
		self.VTable_hash = {}
		self.hash_to_actual_VTable = {}
		self.got_real_vtable_for_key = {}
		self.ctor_vtable_and_unique_VBOs = {}
		self.ctor_to_actual_vtable = {}
		self.scanRodataForVTTs()
		self.vt_obj.remove_VTTs_identified_as_VTables()
		self.getSubVTTs()
		self.recoverAndVerifyVBaseOffsets()

	def getVTTEntriesAbove(self, vtt_entry):
	    #global pure_virtual
	    prevVttEntry = vtt_entry-DWORD_SIZE
	    if in_seg(Dword(prevVttEntry), 'rodata', self.segs) and not Dword(prevVttEntry) == self.vt_obj.pure_virtual: #check if previous entry in possible VTT points to an rodata segment
	        return prevVttEntry
	    else:
	        return -1

	def getVTTTEntriesBelow(self, vtt_entry):
	    nextVttEntry = vtt_entry+DWORD_SIZE
	    if in_seg(Dword(nextVttEntry), 'rodata', self.segs) and not Dword(nextVttEntry) == self.vt_obj.pure_virtual: #check if previous entry in possible VTT points to an rodata segment
	        return nextVttEntry
	    else:
	        return -1

	def scanRodataForVTTs(self):
	    #global VTTs, segs
	    j = len(self.VTTs)
	    for k,currentEA,rodataEndEA in self.segs['rodata']:
	        foundAVTT = False
	        while currentEA <= rodataEndEA:
	            if not j == 0 and currentEA in self.VTTs[j-1]: # if currentEA is already a memeber of last VTT processed
	                currentEA += DWORD_SIZE
	                continue
	            j = self.verifyAVTT(currentEA, j)
	            currentEA += DWORD_SIZE

	def verifyAVTT(self, i, j):
		#global VTTs, VTTEntrys_To_Vtables
		vptr = Dword(i)
		ending = False
		k = 1
		if(in_seg(vptr, 'rodata', self.segs)):
			if vptr in self.vt_obj.vptr_to_top_of_vtable or self.vt_obj.verifyAVtable(vptr):
			    self.VTTs[j] = []
			    self.VTTs[j].append(i)
			    if not i in self.VTTEntrys_To_Vtables:
			        if vptr in self.vt_obj.vptr_to_top_of_vtable:
			            self.VTTEntrys_To_Vtables[i] = self.vt_obj.vptr_to_top_of_vtable[vptr]
			        else:
			           self. VTTEntrys_To_Vtables[i] = vptr
			    
			    nextVttEntry = self.getVTTTEntriesBelow(i)
			    secondEntry = Dword(nextVttEntry)
			    while not nextVttEntry == -1:
			        nextVptr = Dword(nextVttEntry)
			        if ending == True and (nextVptr < vptr or nextVptr > secondEntry): 
			            break
			        if k > 1 and nextVptr > vptr and nextVptr < secondEntry:
			            ending = True
			        if nextVptr in self.vt_obj.vptr_to_top_of_vtable:
			            nextVptr = self.vt_obj.vptr_to_top_of_vtable[nextVptr]
			        if self.vt_obj.verifyAVtable(nextVptr): #another valid entry
			            self.VTTs[j].append(nextVttEntry)
			            if not nextVttEntry in self.VTTEntrys_To_Vtables:
			                self.VTTEntrys_To_Vtables[nextVttEntry] = nextVptr
			        else:
			            break
			        nextVttEntry = self.getVTTTEntriesBelow(nextVttEntry)
			        k += 1
			    
			    if len(self.VTTs[j]) > 1:
			        j+=1
			    else:
			        del self.VTTs[j]
		return j

	def getPossibleVTTs(self):
	    #global VTTs, possible_VTT_Entries
	    j = 0
	    for i in self.possible_VTT_Entries:
	        if not j == 0 and i in self.VTTs[j-1]: # if i is already a memeber of last VTT processed
	            continue
	        j = self.verifyAVTT(i, j)

	def mergeVTables(self): #wh=0 is vptr is for actual VTable, 1 if vptr is for construction VTable
	    #global VTable_hash, hash_to_actual_VTable, vtables, possible_constructorVTables
	    #compute hash
	    for v in self.vt_obj.vtables:
	        key = 0
	        key += self.vt_obj.vtables[v]['typeinfo']
	        if self.vt_obj.vtables[v]['typeinfo'] == 0:
	            for f in self.vt_obj.vtables[v]['vfptrs']:
	                key += f
	        if self.vt_obj.vtables[v]['offsetToTop'] == 0:
	            if not v in self.possible_constructorVTables:#create entry in hash_to_actual_VTable. key:hash, value:this vptr
	                if (v in self.got_real_vtable_for_key and self.got_real_vtable_for_key[v] == 0) or not key in self.hash_to_actual_VTable:
	                    self.hash_to_actual_VTable[key] = v
	                else:
	                	self.got_real_vtable_for_key[v] = 1
	            else:
	                if not key in self.hash_to_actual_VTable:
	                    self.hash_to_actual_VTable[key] = v
	                    self.got_real_vtable_for_key[v] = 0
	            self.VTable_hash[v] = key
	            if v in self.vbaseOffsets and len(self.vbaseOffsets[v]) > 0 and v in self.possible_constructorVTables:
	                if not key in self.ctor_vtable_and_unique_VBOs:
	                    self.ctor_vtable_and_unique_VBOs[key] = set()
	                if not key in self.ctor_to_actual_vtable:
	                    self.ctor_to_actual_vtable[key] = set()
	                self.ctor_vtable_and_unique_VBOs[key].add(self.vbaseOffsets[v][0])
	                self.ctor_to_actual_vtable[key].add(v)

	def getSubVTTs(self):
		#global VTTs, vtables, VTTEntrys_To_Vtables, subVTTs, subVTTKeys, possible_constructorVTables, VTables_To_VTTEntries    
		for j in self.VTTs:
		    ordered_vptrs = []
		    for i in self.VTTs[j]:
		        ordered_vptrs.append(self.VTTEntrys_To_Vtables[i])
		        if not self.VTTEntrys_To_Vtables[i] in self.VTables_To_VTTEntries:
		            self.VTables_To_VTTEntries[self.VTTEntrys_To_Vtables[i]] = i
		    ordered_vptrs.sort()
		    aSubVTTs = {}
		    k = -1
		    for i in ordered_vptrs: 
		    	if i in self.vt_obj.vptr_to_top_of_vtable and self.vt_obj.vptr_to_top_of_vtable[i] in self.vt_obj.vtables:
		    		offsetToTop = self.vt_obj.vtables[self.vt_obj.vptr_to_top_of_vtable[i]]['offsetToTop']
		    	else:
					if not i in self.vt_obj.vtables:
						continue
					offsetToTop = self.vt_obj.vtables[i]['offsetToTop']
		        if offsetToTop == 0:
		            k = i
		            if not k in aSubVTTs:
		                aSubVTTs[k] = []
		            self.subVTTKeys.append(self.VTables_To_VTTEntries[k])
		            aSubVTTs[k].append(i)
		            if self.VTTEntrys_To_Vtables[self.VTTs[j][0]] != i:
		                self.possible_constructorVTables.add(i)
		        else:
		            if k == -1: continue
		            aSubVTTs[k].append(i)
		    self.subVTTs[self.VTTs[j][0]] = aSubVTTs

	def recoverAndVerifyVBaseOffsets(self):
	    #global subVTTs, vbaseOffsets, vtables
	    firstVbaseLoc = 24
	    for j in self.subVTTs:
	        for i in self.subVTTs[j]:
	            if i in self.vt_obj.top_of_vtable_tovptr:
	                vptr = self.vt_obj.top_of_vtable_tovptr[i]
	            else:
	                vptr = i
	            vbaseLoc = firstVbaseLoc
	            curVbaseoffsetLoc = vptr-vbaseLoc
	            self.vbaseOffsets[i] = []
	            k = 1
	            while k < len(self.subVTTs[j][i]) :
	                offsetToTop = 0
	                if self.subVTTs[j][i][k] in self.vt_obj.vptr_to_top_of_vtable:
	                    offsetToTop = self.vt_obj.vtables[self.vt_obj.vptr_to_top_of_vtable[self.subVTTs[j][i][k]]]['offsetToTop']
	                elif self.subVTTs[j][i][k] in self.vt_obj.vtables:
	                    offsetToTop = self.vt_obj.vtables[self.subVTTs[j][i][k]]['offsetToTop']
	                if Dword(curVbaseoffsetLoc) + offsetToTop == 0x100000000 or Dword(curVbaseoffsetLoc) + offsetToTop == 0x0:
	                    self.vbaseOffsets[i].append(Dword(curVbaseoffsetLoc))
	                    curVbaseoffsetLoc -= DWORD_SIZE
	                if vptr > i:
	                    if Dword(i) + offsetToTop == 0x100000000 or Dword(i) + offsetToTop == 0x0:
	                        self.vbaseOffsets[i].append(Dword(i))
	                        curVbaseoffsetLoc -= DWORD_SIZE
	                k += 1

	def get_distinct_virtual_bases(self, cd_obj):
	    global parsedInstns, func_vt, ctor_dtor_vt, vbaseOffsets, call_instns, distinctVBases, vptr_to_top_of_vtable, firstVTTWrites
	    global vptr_writes
	    for v in self.vbaseOffsets:
	        if v in cd_obj.ctor_dtor_vt:
	            for cd in cd_obj.ctor_dtor_vt[v]:
	                if cd in cd_obj.call_instns:
	                    for (ea, callee) in cd_obj.call_instns[cd]:
	                        if cd in cd_obj.firstVTTWrites and ea >cd_obj.firstVTTWrites[cd]: continue
	                        if in_seg(callee, 'plt', self.segs):
	                            decode_insn(callee)
	                            if cmd.itype == 88: #NN_jmp is 86, but I need 88. I will check the mnemonic for 88
	                                if not in_seg(cmd.Operands[0].addr, 'code', self.segs):
	                                    callee = Dword(cmd.Operands[0].addr)
	                                else:
	                                    callee = cmd.Operands[0].addr
	                        if callee in cd_obj.func_vt and ea in cd_obj.parsedInstns:
	                            objAddrs = cd_obj.parsedInstns[ea]
	                            for off in objAddrs:
	                            	if 7 in objAddrs[off] and off in self.vbaseOffsets[v]:
	                                    if not v in self.distinctVBases:
	                                        self.distinctVBases[v] = set()
	                                    if cd_obj.func_vt[callee] in self.vt_obj.top_of_vtable_tovptr:
	                                        self.distinctVBases[v].add(self.vt_obj.top_of_vtable_tovptr[cd_obj.func_vt[callee]])
	                                    else:
	                                        self.distinctVBases[v].add(cd_obj.func_vt[callee])
	                if cd in cd_obj.vptr_writes:
	                    for w in cd_obj.vptr_writes[cd]:
	                        if cd_obj.vptr_writes[cd][w]['offset'] in self.vbaseOffsets[v]:
	                            if not v in self.distinctVBases:
	                                self.distinctVBases[v] = set()
	                            self.distinctVBases[v].add(w)
	        elif v in self.vt_obj.top_of_vtable_tovptr and self.vt_obj.top_of_vtable_tovptr[v] in cd_obj.ctor_dtor_vt:
	            for cd in cd_obj.ctor_dtor_vt[self.vt_obj.top_of_vtable_tovptr[v]]:
	                for (ea, callee) in cd_obj.call_instns[cd]:
	                    if cd in cd_obj.firstVTTWrites and ea > cd_obj.firstVTTWrites[cd]: continue
	                    if in_seg(callee, 'plt', self.segs):
	                        decode_insn(callee)
	                        if cmd.itype == 88: #NN_jmp is 86, but 88 is needed.
	                            if not in_seg(cmd.Operands[0].addr, 'text', self.segs):
	                                callee = Dword(cmd.Operands[0].addr)
	                            else:
	                                callee = cmd.Operands[0].addr
	                    if callee in cd_obj.func_vt:
	                        objAddrs = cd_obj.parsedInstns[ea]
	                        for off in objAddrs:
	                            if 7 in objAddrs[off] and off in self.vbaseOffsets[v]:
	                                if not v in self.distinctVBases:
	                                    self.distinctVBases[v] = set()
	                                if cd_obj.func_vt[callee] in self.vt_obj.top_of_vtable_tovptr:
	                                    self.distinctVBases[v].add(self.vt_obj.top_of_vtable_tovptr[cd_obj.func_vt[callee]])
	                                else:
	                                    self.distinctVBases[v].add(cd_obj.func_vt[callee])
	                if cd in cd_obj.vptr_writes:
	                    for w in cd_obj.vptr_writes[cd]:
	                        if cd_obj.vptr_writes[cd][w]['offset'] in self.vbaseOffsets[v]:
	                            if not v in self.distinctVBases:
	                                self.distinctVBases[v] = set()
	                            self.distinctVBases[v].add(w)

	def get_intermediate_bases(self, cd_obj):
	    #global list_of_ctor_dtors, VTT_addr_write_instns, func_vt, VTable_hash, hash_to_actual_VTable, intermediate_bases, distinctVBases
	    for f in cd_obj.VTT_addr_write_instns:
	        if not f in cd_obj.func_vt:
	            continue
	        vptr = cd_obj.func_vt[f]
	        for i in cd_obj.VTT_addr_write_instns[f]:
	            if not i in self.VTTEntrys_To_Vtables: continue
	            if self.VTTEntrys_To_Vtables[i] in self.vt_obj.vptr_to_top_of_vtable:
	                self.vptr_of_VTT_entry = self.vt_obj.vptr_to_top_of_vtable[self.VTTEntrys_To_Vtables[i]]
	            else:
	                self.vptr_of_VTT_entry = self.VTTEntrys_To_Vtables[i]
	            if vptr in self.vt_obj.vptr_to_top_of_vtable and self.vptr_of_VTT_entry in self.VTable_hash and self.VTable_hash[self.vptr_of_VTT_entry] in self.hash_to_actual_VTable and self.vt_obj.vptr_to_top_of_vtable[vptr] == self.hash_to_actual_VTable[self.VTable_hash[self.vptr_of_VTT_entry]]: continue    
	            if self.vptr_of_VTT_entry in self.VTable_hash and self.VTable_hash[self.vptr_of_VTT_entry] in self.hash_to_actual_VTable:
	                if not vptr in self.intermediate_bases:
	                    self.intermediate_bases[vptr] = set()
	                self.intermediate_bases[vptr].add(self.hash_to_actual_VTable[self.VTable_hash[self.vptr_of_VTT_entry]])


	def get_rem_intermediates(self):
	    #global subVTTs, vptr_to_top_of_vtable, VTable_hash, hash_to_actual_VTable, intermediate_bases
	    for v in self.subVTTs:
	        vptr = Dword(v)
	        if vptr in self.vt_obj.vptr_to_top_of_vtable:
	            vptr = self.vt_obj.vptr_to_top_of_vtable[vptr]
	        for each in self.subVTTs[v]:
	            if each == vptr: continue
	            if each in self.VTable_hash and self.VTable_hash[each] in self.hash_to_actual_VTable:
	                if not vptr in self.intermediate_bases:
	                    self.intermediate_bases[vptr] = set()
	                self.intermediate_bases[vptr].add(self.hash_to_actual_VTable[self.VTable_hash[each]])

	def finalize_virtual_inher(self):
	    #global intermediate_bases, distinctVBases
	    loop_intermediate_bases = copy.deepcopy(self.intermediate_bases)
	    for d in loop_intermediate_bases:
	        if d in self.distinctVBases and len(self.distinctVBases[d]) == 1:
	            for b in loop_intermediate_bases[d]:
	                if not b in self.distinctVBases:
	                    self.distinctVBases[b] = self.distinctVBases[d]
	                if b in self.intermediate_bases:
	                    rem = set(self.intermediate_bases[b]) - set(self.intermediate_bases[d])
	                    if len(rem) > 0:
	                        for r in rem:
	                            self.intermediate_bases[d].add(r)
	        if not d in self.distinctVBases:
	            for b in loop_intermediate_bases[d]:
	                if b in self.distinctVBases:
	                    self.distinctVBases[d] = set()
	                    for v in self.distinctVBases[b]:
	                        self.distinctVBases[d].add(v)

def main():
    # global all_immediates, vtables, possible_VTT_Entries, VTTs, VTTEntrys_To_Vtables, subVTTs, vbaseOffsets, distinctVBases, subVTTKeys, VTT_addr_write_instns
    # global VTable_hash, hash_to_actual_VTable, intermediate_bases, possible_constructorVTables, vtables_names, ctor_vtable_and_unique_VBOs
    # global list_of_ctor_dtors

    segs = buildsegmap()
    vt_obj = VTablesAnalysis(segs)
    vi_obj = VirtualInheritanceAnalysis(segs, vt_obj)
    cd_obj = CtorDtorAnalysis(segs, vt_obj.vtables, vt_obj.top_of_vtable_tovptr, vi_obj.subVTTKeys)
    vi_obj.get_distinct_virtual_bases(cd_obj)
    vi_obj.mergeVTables()
    vi_obj.get_intermediate_bases(cd_obj)
    vi_obj.finalize_virtual_inher()
    vi_obj.get_rem_intermediates()




    print('Derived class [Virtual Bases] [Intermediate Bases]')
    for d in vi_obj.distinctVBases:
        if d in vi_obj.intermediate_bases:
            print format(d, 'x'), [format(b, 'x') for b in vi_obj.distinctVBases[d]], [format(i, 'x') for i in vi_obj.intermediate_bases[d]]
        else: 
            print format(d, 'x'), [format(b, 'x') for b in vi_obj.distinctVBases[d]]

if __name__ == "__main__":
	main()