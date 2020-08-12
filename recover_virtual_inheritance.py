import ctypes
import idc
import idascript
#import matplotlib.pyplot as plt
from idaapi import *
try:
    import cPickle as pickle
except:
    import pickle
import copy
segs = {}
DWORD_SIZE = 8
pure_virtual = 0
immediates_n_address = []
validFunctions = []
vtables = {}
vfns = {}
sec_vptrs_to_address = {}
has_vir_dtor = []
vptr_to_top_of_vtable = {}
top_of_vtable_tovptr = {}
ctor_dtor_vt = {}
func_vt = {}
call_instns = {}
list_of_ctor_dtors = []
VTT_addr_write_instns = {}
ctor_dtors = {}
parsedInstns = {} 
firstVTTWrites = {} 
vptr_writes = {} 
VTTs = {}
VTTEntrys_To_Vtables = {}
all_immediates = set()
possible_VTT_Entries = []
subVTTs = {}
subVTTKeys = []
possible_constructorVTables = set()
VTables_To_VTTEntries = {}
vbaseOffsets = {}
distinctVBases = {}
intermediate_bases = {}

####################Start of functions that gather VTables###########################
def buildsegmap():
	global segs
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
		pmsg = '{0} @ {1}, size = {2}, perm = {3}, type = {4}\n'.format(sname, hex(seg.startEA), seg.size(), seg.perm, seg.type) #removed to compute exec time
		msg(pmsg) #removed to compute exec time
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
	return

def in_seg(val, segname):
	global segs
	if val == 0:
		return False
	for k,n,m in segs[segname]:
		if val >= n and val < m:
			return True
	return False

def is_abst_class(pv):
	while True:
		if (Dword(pv) == 0 and Dword(pv + DWORD_SIZE) == 0):
			return True
		elif in_seg(Dword(pv), 'code') or pure_v(Dword(pv)):
			pv = pv + DWORD_SIZE
		else:
			return False

def pure_v(addr):
	global pure_virtual
	if addr == 0x0: return True
	if get_func_name(addr) == "__cxa_pure_virtual":
		if pure_virtual == 0:
			pure_virtual = addr
		return True
	else:
		decode_insn(addr)
		next_addr = cmd.Operands[0].addr
		if in_seg(next_addr, 'got_plt'):
			if get_func_name(Dword(next_addr)) == "__cxa_pure_virtual":
				return True
		return False

def get_got_entry(addr):
	return Dword(addr)

def gatherImmediates():
	global immediates_n_address
	potentials = set()
	for i in range(get_func_qty()):
		func = getn_func(i)
		validFunctions.append(func.startEA)
		for ea in range(func.startEA, func.endEA):
			flags = get_flags_novalue(ea)
			if isHead(flags) and isCode(flags):
				if decode_insn(ea) == 0:
					continue
				for j in range(6):
					if cmd.Operands[j].type == o_imm:
						imm_val = cmd.Operands[j].value
						if in_seg(imm_val, 'rodata'):
							potentials.add(imm_val)
							immediates_n_address.append((imm_val, 'd', ea))
					elif cmd.Operands[j].type == o_mem:
						imm_val = cmd.Operands[j].addr
						if in_seg(imm_val, 'rodata'):
							potentials.add(imm_val)
							immediates_n_address.append((imm_val, 'd', ea))
						elif in_seg(imm_val, 'got'):
							potentials.add(imm_val)
							immediates_n_address.append((imm_val, 'i', ea))

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
								if in_seg(imm_val, 'rodata'):
									potentials.add(imm_val)
									immediates_n_address.append((imm_val, 'd', ea))
							elif cmd.Operands[j].type == o_mem:
								imm_val = cmd.Operands[j].addr
								if in_seg(imm_val, 'rodata'):
									potentials.add(imm_val)
									immediates_n_address.append((imm_val, 'd', ea))
								elif in_seg(imm_val, 'got'):
									potentials.add(imm_val)
									immediates_n_address.append((imm_val, 'i', ea))

				ok = fti.next()

	return potentials

def get_vptr_from_top_address(ea):
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

def is_top_of_vtable(v, ea):
	poss_offset_added = get_vptr_from_top_address(ea)
	if not poss_offset_added == False:
		new_addr = v + poss_offset_added
		if in_seg(Dword(new_addr), 'text') or pure_v(Dword(new_addr)) or in_seg(Dword(new_addr-DWORD_SIZE), 'rodata'):
			return (True, new_addr)
	if not type(Dword(v + DWORD_SIZE)) in {int, long} :
		return (False, 0)
	if ((Dword(v - DWORD_SIZE) == 0 or in_seg(Dword(v - DWORD_SIZE), 'rodata')) and Dword(v - DWORD_SIZE*2) == 0 and 
			((get_func_name(Dword(v)) == "__cxa_pure_virtual") or in_seg(Dword(v), 'code'))):
		return (False, 0)
	if ( (not in_seg(Dword(v - DWORD_SIZE), 'rodata') or get_func_name(Dword(v - DWORD_SIZE)) == "__cxa_pure_virtual" or 
			(in_seg(Dword(v - DWORD_SIZE), 'rodata') and not get_func_name(Dword(v + DWORD_SIZE)) == "__cxa_pure_virtual") and not in_seg(Dword(v + DWORD_SIZE), 'code')) and
			(in_seg(Dword(v + DWORD_SIZE), 'rodata') or Dword(v + DWORD_SIZE) == 0) ):
		return (True, v)
	else:
		return (False, 0)

def verifyAVtable(pv, typ='n', ea=-1):
	global vtables, sec_vptrs_to_address, has_vir_dtor, vptr_to_top_of_vtable, top_of_vtable_tovptr
	if pure_virtual != 0 and (pv == pure_virtual or Dword(pv) == pure_virtual):
		return False
	if pv in vtables or Dword(pv) in vtables:
		if ea == -1 or (pv in top_of_vtable_tovptr and (top_of_vtable_tovptr[pv] - pv) < get_vptr_from_top_address(ea)) or ((Dword(pv) in top_of_vtable_tovptr and (top_of_vtable_tovptr[Dword(pv)] - Dword(pv)) < get_vptr_from_top_address(ea))):
			return True
	if pv in vptr_to_top_of_vtable or Dword(pv) in vptr_to_top_of_vtable:
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
				offset_actual_vptr_possibly = get_vptr_from_top_address(ea)
				if not offset_actual_vptr_possibly == False:
					pv = p_vtp + offset_actual_vptr_possibly
				else:
					pv = p_vtp + (DWORD_SIZE * 2)
		else:
		    (is_top, new_addr) = is_top_of_vtable(pv, ea);
		    if is_top:
		        pv = new_addr
	entry = Dword(pv)
	typeinfoptr = Dword(pv - DWORD_SIZE)
	if (not in_seg(typeinfoptr, 'rodata')) and (entry != 0 or Dword(pv + DWORD_SIZE) != 0 or (not in_seg(Dword(pv + (DWORD_SIZE *2)), 'code') and not pure_v(Dword(pv + (DWORD_SIZE *2))) and not pure_v(Dword(pv)))) and (not in_seg(entry, 'code') and not pure_v(Dword(pv + (DWORD_SIZE *2))) and not pure_v(Dword(pv))):
	    return False #meaning address not a vtable

	if (typeinfoptr != 0) and (not in_seg(typeinfoptr, 'rodata')): return False #meaning address not a vtable
	vtable = {}
	if (is_abst_class(pv)):
	    vtable['abst'] = True
	else:
	    vtable['abst'] = False
	vtable['address'] = pv
	vtable['vfptrs'] = []
	vtable['secondaries'] = []

	vtable['vfptrs'].append(entry)

	if (entry == 0 and Dword(pv + DWORD_SIZE) == 0):
	    has_vir_dtor.append(pv)
	    curr = 3
	else:
	    curr = 1
	zero_entries = 0
	while True:
	    entry = Dword(pv + curr * DWORD_SIZE)
	    curr += 1
	    if (in_seg(entry, 'code') and entry in validFunctions) or pure_v(entry) or in_seg(entry, 'extern'):
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

	if vtable['offsetToTop'] != 0 and real_pv in vtables:
	    if not ea == -1:
	        sec_vptrs_to_address[ea] = pv
	    vtables[pv] = vtable
	else:
	    vtables[real_pv] = vtable
	if ea != -1 and real_pv in vtables: #only do this if vptr gotten from text section, not from VTT
	    if pv in vptr_to_top_of_vtable:
	        del top_of_vtable_tovptr[vptr_to_top_of_vtable[pv]]
	    if real_pv in top_of_vtable_tovptr:
	        del vptr_to_top_of_vtable[top_of_vtable_tovptr[real_pv]]
	    vptr_to_top_of_vtable[pv] = real_pv
	    top_of_vtable_tovptr[real_pv] = pv
	return True #meaning that the address is indeed a vtables

def verifyVTables():
    global vtables
    global segs
    global vfns
    global sec_vptrs_to_address, has_vir_dtor, vptr_to_top_of_vtable, top_of_vtable_tovptr
    global all_immediates
    global immediates_n_address
    imm_val = 0

    for (pv, typ, ea) in immediates_n_address:
        verifyAVtable(pv, typ, ea)
    remove_VTTs_identified_as_VTables()
    return

def remove_VTTs_identified_as_VTables():
    global vtables, vfns
    for v in vtables.keys():
        for f in vtables[v]['vfptrs']:
            if f in vtables and not in_seg(f, "extern"):
                del vtables[v]
                break
            f_ptr = get_func(f)
            if not f_ptr is None:
                if get_func(f).startEA == f:
                    vfns[f] = True

####################End of functions that gather VTables###########################

####################Start of functions that identify ctors and dtors###########################
def identify_ctor_dtor():
    global vtables, ctor_dtor_vt, list_of_ctor_dtors, VTT_addr_write_instns, ctor_dtors, func_vt, call_instns
    
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
                        if cmd.Operands[j].value in vtables or cmd.Operands[j].value in top_of_vtable_tovptr:
                            if cmd.Operands[j].value in vtables:
                                vta = cmd.Operands[j].value
                            else:
                                vta = top_of_vtable_tovptr[cmd.Operands[j].value]
                            if not func.startEA in ctor_dtors:
                                ctor_dtors[func.startEA] = []
                            ctor_dtors[func.startEA].append(vta)
                            list_of_ctor_dtors.append((func.startEA, func.endEA))
                        


                    if cmd.Operands[j].type == o_mem:
                        ptr = cmd.Operands[j].addr
                        if in_seg(ptr, 'got'):
                            ptr = get_got_entry(ptr)
                        if ptr in vtables or ptr in top_of_vtable_tovptr:
                            if ptr in vtables:
                                pass
                            else:
                                ptr = top_of_vtable_tovptr[ptr]
                            if not func.startEA in ctor_dtors:
                                ctor_dtors[func.startEA] = []
                            ctor_dtors[func.startEA].append(ptr)
                            list_of_ctor_dtors.append((func.startEA, func.endEA))
                        
                
                if cmd.itype == NN_call or cmd.itype == NN_jmp:
                    if not func.startEA in call_instns:
                        call_instns[func.startEA] = []
                    call_instns[func.startEA].append((ea, cmd.Operands[0].addr))  

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
                                if cmd.Operands[j].value in vtables or cmd.Operands[j].value in top_of_vtable_tovptr:
                                    if cmd.Operands[j].value in vtables:
                                        vta = cmd.Operands[j].value
                                    else:
                                        vta = top_of_vtable_tovptr[cmd.Operands[j].value]
                                    if not func.startEA in ctor_dtors:
                                        ctor_dtors[func.startEA] = []
                                    ctor_dtors[func.startEA].append(vta)
                                    list_of_ctor_dtors.append((func.startEA, func.endEA))
                                

                            if cmd.Operands[j].type == o_mem:
                                ptr = cmd.Operands[j].addr
                                if in_seg(ptr, 'got'):
                                    ptr = get_got_entry(ptr)
                                if ptr in vtables or ptr in top_of_vtable_tovptr:
                                    if ptr in vtables:
                                        pass
                                    else:
                                        ptr = top_of_vtable_tovptr[ptr]
                                    if not func.startEA in ctor_dtors:
                                        ctor_dtors[func.startEA] = []
                                    ctor_dtors[func.startEA].append(ptr)
                                    list_of_ctor_dtors.append((func.startEA, func.endEA))
                                

                        if cmd.itype == NN_call or cmd.itype == NN_jmp:
                            if not func.startEA in call_instns:
                                call_instns[func.startEA] = []
                            call_instns[func.startEA].append((ea, cmd.Operands[0].addr))
                ok = fti.next()

def assign_vptr_to_ctor_dtor():
    global ctor_dtors, ctor_dtor_vt, func_vt, vptr_writes

    for f,v in ctor_dtors.items():
        is_set = 0
        if f in vptr_writes:
            ea = 0
            owner_vptr = -1
            for vp in vptr_writes[f]:
                if vptr_writes[f][vp]['addr'] > ea and vptr_writes[f][vp]['offset'] == 0:
                    ea = vptr_writes[f][vp]['addr']
                    owner_vptr = vp
            if owner_vptr != -1 and owner_vptr in vtables and vtables[owner_vptr]['offsetToTop'] == 0:
                if not owner_vptr in ctor_dtor_vt:
                    ctor_dtor_vt[owner_vptr] = []
                ctor_dtor_vt[owner_vptr].append(f)
                func_vt[f] = owner_vptr
                is_set = 1
        if is_set == 0:   
            for k in v:
                if not k in vtables:
                    continue
                if vtables[k]['offsetToTop'] == 0: # This is the complete obj!
                    if not k in ctor_dtor_vt:
                        ctor_dtor_vt[k] = []
                    ctor_dtor_vt[k].append(f)
                    func_vt[f] = k
                    break

####################End of functions that identify ctors and dtors###########################

####################Start of functions that parse instructions in ctors and dtors to############################
#These set of functions help us know the offset within an object that is stored in rdi before making a ctor or dtor call
def add_remove_elem(objAddrs, reg1, reg2):
    for off in objAddrs:
        if reg1 in objAddrs[off]:
            objAddrs[off].remove(reg1)
            break
    for off in objAddrs:
        if reg2 in objAddrs[off]:
            objAddrs[off].append(reg1)
            break
    return objAddrs

def create_new_offset_entry(objAddrs, offset, reg1):
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

def parseFuncs():
    global parsedInstns, VTT_addr_write_instns, list_of_ctor_dtors, firstVTTWrites, vptr_writes, subVTTKeys
    for (s, e) in list_of_ctor_dtors:
        reg_with_vtt_address = -1
        current_vtt_address = -1 
        reg_vptr_write_moves = {}
        current_obj_addr = set()
        current_obj_addr.add(7)
        objAddrs = {}
        objAddrs[0] = []
        objAddrs[0].append(7)
        vptr_writes[s] = {}
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
                if in_seg(cmd.Operands[1].addr, 'got'):
                    imm_addr = Dword(cmd.Operands[1].addr)
                else:
                    imm_addr = cmd.Operands[1].addr
                if imm_addr in subVTTKeys:
                    current_vtt_address = imm_addr
                    reg_with_vtt_address = cmd.Operands[0].reg
                    if cmd.Operands[0].reg == 6:
                        if not s in VTT_addr_write_instns:
                            VTT_addr_write_instns[s] = set()
                            firstVTTWrites[s] = ea 
                        VTT_addr_write_instns[s].add(current_vtt_address)
                        current_vtt_address = -1 
                    continue
                if imm_addr in vtables and not imm_addr in vptr_writes[s]:
                    vptr = imm_addr
                    vptr_writes[s][vptr] = {}
                    vptr_writes[s][vptr]['addr'] = ea
                    vptr_writes[s][vptr]['offset'] = -1
                    reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
                    continue
                if imm_addr in top_of_vtable_tovptr and not imm_addr in vptr_writes[s]:
                    vptr = top_of_vtable_tovptr[imm_addr]
                    vptr_writes[s][vptr] = {}
                    vptr_writes[s][vptr]['addr'] = ea
                    vptr_writes[s][vptr]['offset'] = -1
                    reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
                    continue
            elif cmd.Operands[1].type == o_imm:
                if cmd.Operands[0].reg in current_obj_addr:
                    current_obj_addr.remove(cmd.Operands[0].reg)
                if cmd.Operands[1].value in subVTTKeys:
                    current_vtt_address = cmd.Operands[1].value
                    reg_with_vtt_address = cmd.Operands[0].reg
                    if cmd.Operands[0].reg == 6:
                        if not s in VTT_addr_write_instns:
                            VTT_addr_write_instns[s] = set()
                            firstVTTWrites[s] = ea
                        VTT_addr_write_instns[s].add(current_vtt_address)
                        current_vtt_address = -1
                    continue
                if cmd.Operands[1].value in vtables and not cmd.Operands[1].value in vptr_writes:
                    vptr = cmd.Operands[1].value
                    vptr_writes[s][vptr] = {}
                    vptr_writes[s][vptr]['addr'] = ea
                    vptr_writes[s][vptr]['offset'] = -1
                    reg_vptr_write_moves[cmd.Operands[0].reg] = vptr
                    continue
                if cmd.Operands[1].value in top_of_vtable_tovptr and not top_of_vtable_tovptr[cmd.Operands[1].value] in vptr_writes:
                    vptr = top_of_vtable_tovptr[cmd.Operands[1].value]
                    vptr_writes[s][vptr]={}
                    vptr_writes[s][vptr]['addr'] = ea
                    vptr_writes[s][vptr]['offset'] = -1
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
                if not s in VTT_addr_write_instns:
                    VTT_addr_write_instns[s] = set()
                    firstVTTWrites[s] = ea
                VTT_addr_write_instns[s].add(current_vtt_address + vtt_offset)
                current_vtt_address = -1

            elif cmd.Operands[0].reg in reg_vptr_write_moves and cmd.itype in {NN_lea, NN_mov} and cmd.Operands[0].type == o_reg:
                del reg_vptr_write_moves[cmd.Operands[0].reg]
            elif cmd.Operands[1].reg in reg_vptr_write_moves and cmd.itype in {NN_lea, NN_mov}:
                if cmd.Operands[0].type == o_reg:
                    reg_vptr_write_moves[cmd.Operands[0].reg] = reg_vptr_write_moves[cmd.Operands[1].reg]
                elif cmd.Operands[0].type == o_phrase and cmd.Operands[0].reg in current_obj_addr and cmd.Operands[1].type == o_reg: #mov [rdi], reg
                    vptr = reg_vptr_write_moves[cmd.Operands[1].reg]
                    if vptr in vptr_writes[s]:
                        vptr_writes[s][vptr]['offset'] = 0
                        vptr_writes[s][vptr]['addr'] = ea
                        del reg_vptr_write_moves[cmd.Operands[1].reg]
                elif cmd.Operands[0].type == o_displ and cmd.Operands[0].reg in current_obj_addr and cmd.Operands[1].type == o_reg: #mov [rdi+x], reg
                    vptr = reg_vptr_write_moves[cmd.Operands[1].reg]
                    if vptr in vptr_writes[s] and (vptr_writes[s][vptr]['offset'] != 0 or cmd.Operands[0].addr == 0):
                        vptr_writes[s][vptr]['offset'] = cmd.Operands[0].addr
                        vptr_writes[s][vptr]['addr'] = ea
                        del reg_vptr_write_moves[cmd.Operands[1].reg]
            if cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_reg and cmd.itype == NN_mov:
                reg1 = cmd.Operands[0].reg 
                reg2 = cmd.Operands[1].reg
                objAddrs = add_remove_elem(objAddrs, reg1, reg2)

            elif cmd.Operands[0].type == o_displ and cmd.Operands[1].type == o_reg and cmd.itype == NN_mov :
                offset = cmd.Operands[0].addr
                reg1 = str(cmd.Operands[0].reg)+"+"+str(offset)#
                reg2 = cmd.Operands[1].reg
                objAddrs = add_remove_elem(objAddrs, reg1, reg2)

            elif cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_displ and cmd.itype == NN_mov:
                reg1 = cmd.Operands[0].reg
                offset = cmd.Operands[1].addr
                reg2 = str(cmd.Operands[1].reg)+"+"+str(offset)
                objAddrs = add_remove_elem(objAddrs, reg1, reg2)

            elif cmd.Operands[0].type == o_reg and cmd.Operands[1].type == o_displ and cmd.itype == NN_lea:
                reg1 = cmd.Operands[0].reg
                offset = cmd.Operands[1].addr
                reg2 = cmd.Operands[1].reg
                if current_vtt_address != -1 and reg2 == reg_with_vtt_address:
                    current_vtt_address += offset
                    continue
                objAddrs = create_new_offset_entry(objAddrs, offset, reg2)
                objAddrs = add_remove_elem(objAddrs, reg1, reg2)

            elif (cmd.Operands[0].type == o_reg or cmd.Operands[0].type == o_displ) and (cmd.Operands[1].type == o_imm or cmd.Operands[1].type == o_mem) and cmd.itype == NN_lea:
                reg1 = cmd.Operands[0].reg
                for off in objAddrs:
                    if  reg1 in objAddrs[off]:
                        objAddrs[off].remove(reg1)
                        break
            elif cmd.Operands[0].type == o_reg and cmd.itype == NN_add:
                reg1 = cmd.Operands[0].reg
                offset = cmd.Operands[1].value
                objAddrs = create_new_offset_entry(objAddrs, offset, reg1)
            parsedInstns[ea] = copy.deepcopy(objAddrs)
####################End of functions that parse instructions in ctors and dtors to############################

####################Start of functions that identify virtual inheritance###########################
def getVTTEntriesAbove(vtt_entry):
    global pure_virtual
    prevVttEntry = vtt_entry-DWORD_SIZE
    if in_seg(Dword(prevVttEntry), 'rodata') and not Dword(prevVttEntry) == pure_virtual: #check if previous entry in possible VTT points to an rodata segment
        return prevVttEntry
    else:
        return -1

def getVTTTEntriesBelow(vtt_entry):
    nextVttEntry = vtt_entry+DWORD_SIZE
    if in_seg(Dword(nextVttEntry), 'rodata') and not Dword(nextVttEntry) == pure_virtual: #check if previous entry in possible VTT points to an rodata segment
        return nextVttEntry
    else:
        return -1

def scanRodataForVTTs():
    global VTTs, segs
    j = len(VTTs)
    for k,currentEA,rodataEndEA in segs['rodata']:
        foundAVTT = False
        while currentEA <= rodataEndEA:
            if not j == 0 and currentEA in VTTs[j-1]: # if currentEA is already a memeber of last VTT processed
                currentEA += DWORD_SIZE
                continue
            j = verifyAVTT(currentEA, j)
            currentEA += DWORD_SIZE

def verifyAVTT(i, j):
    global VTTs, VTTEntrys_To_Vtables
    vptr = Dword(i)
    ending = False
    k = 1
    if(in_seg(vptr, 'rodata')):
        if vptr in vptr_to_top_of_vtable or verifyAVtable(vptr):
            VTTs[j] = []
            VTTs[j].append(i)
            if not i in VTTEntrys_To_Vtables:
                if vptr in vptr_to_top_of_vtable:
                    VTTEntrys_To_Vtables[i] = vptr_to_top_of_vtable[vptr]
                else:
                    VTTEntrys_To_Vtables[i] = vptr
            
            nextVttEntry = getVTTTEntriesBelow(i)
            secondEntry = Dword(nextVttEntry)
            while not nextVttEntry == -1:
                nextVptr = Dword(nextVttEntry)
                if ending == True and (nextVptr < vptr or nextVptr > secondEntry): 
                    break
                if k > 1 and nextVptr > vptr and nextVptr < secondEntry:
                    ending = True
                if nextVptr in vptr_to_top_of_vtable:
                    nextVptr = vptr_to_top_of_vtable[nextVptr]
                if verifyAVtable(nextVptr): #another valid entry
                    VTTs[j].append(nextVttEntry)
                    if not nextVttEntry in VTTEntrys_To_Vtables:
                        VTTEntrys_To_Vtables[nextVttEntry] = nextVptr
                else:
                    break
                nextVttEntry = getVTTTEntriesBelow(nextVttEntry)
                k += 1
            
            if len(VTTs[j]) > 1:
                j+=1
            else:
                del VTTs[j]
    return j

def getPossibleVTTs():
    global VTTs, possible_VTT_Entries
    j = 0
    for i in possible_VTT_Entries:
        if not j == 0 and i in VTTs[j-1]: # if i is already a memeber of last VTT processed
            continue
        j = verifyAVTT(i, j)

def mergeVTables(): #wh=0 is vptr is for actual VTable, 1 if vptr is for construction VTable
    global VTable_hash, hash_to_actual_VTable, vtables, possible_constructorVTables
    #compute hash
    for v in vtables:
        key = 0
        key += vtables[v]['typeinfo']
        if vtables[v]['typeinfo'] == 0:
            for f in vtables[v]['vfptrs']:
                key += f
        if vtables[v]['offsetToTop'] == 0:
            if not v in possible_constructorVTables:#create entry in hash_to_actual_VTable. key:hash, value:this vptr
                if (v in got_real_vtable_for_key and got_real_vtable_for_key[v] == 0) or not key in hash_to_actual_VTable:
                    hash_to_actual_VTable[key] = v
                else:
                	got_real_vtable_for_key[v] = 1
            else:
                if not key in hash_to_actual_VTable:
                    hash_to_actual_VTable[key] = v
                    got_real_vtable_for_key[v] = 0
            VTable_hash[v] = key
            if v in vbaseOffsets and len(vbaseOffsets[v]) > 0 and v in possible_constructorVTables:
                if not key in ctor_vtable_and_unique_VBOs:
                    ctor_vtable_and_unique_VBOs[key] = set()
                if not key in ctor_to_actual_vtable:
                    ctor_to_actual_vtable[key] = set()
                ctor_vtable_and_unique_VBOs[key].add(vbaseOffsets[v][0])
                ctor_to_actual_vtable[key].add(v)

def getSubVTTs():
	global VTTs, vtables, VTTEntrys_To_Vtables, subVTTs, subVTTKeys, possible_constructorVTables, VTables_To_VTTEntries    
	for j in VTTs:
	    ordered_vptrs = []
	    for i in VTTs[j]:
	        ordered_vptrs.append(VTTEntrys_To_Vtables[i])
	        if not VTTEntrys_To_Vtables[i] in VTables_To_VTTEntries:
	            VTables_To_VTTEntries[VTTEntrys_To_Vtables[i]] = i
	    ordered_vptrs.sort()
	    aSubVTTs = {}
	    k = -1
	    for i in ordered_vptrs: 
	    	if i in vptr_to_top_of_vtable and vptr_to_top_of_vtable[i] in vtables:
	    		offsetToTop = vtables[vptr_to_top_of_vtable[i]]['offsetToTop']
	    	else:
				if not i in vtables:
					continue
				offsetToTop = vtables[i]['offsetToTop']
	        if offsetToTop == 0:
	            k = i
	            if not k in aSubVTTs:
	                aSubVTTs[k] = []
	            subVTTKeys.append(VTables_To_VTTEntries[k])
	            aSubVTTs[k].append(i)
	            if VTTEntrys_To_Vtables[VTTs[j][0]] != i:
	                possible_constructorVTables.add(i)
	        else:
	            if k == -1: continue
	            aSubVTTs[k].append(i)
	    subVTTs[VTTs[j][0]] = aSubVTTs

def recoverAndVerifyVBaseOffsets():
    global subVTTs, vbaseOffsets, vtables
    firstVbaseLoc = 24
    for j in subVTTs:
        for i in subVTTs[j]:
            if i in top_of_vtable_tovptr:
                vptr = top_of_vtable_tovptr[i]
            else:
                vptr = i
            vbaseLoc = firstVbaseLoc
            curVbaseoffsetLoc = vptr-vbaseLoc
            vbaseOffsets[i] = []
            k = 1
            while k < len(subVTTs[j][i]) :
                offsetToTop = 0
                if subVTTs[j][i][k] in vptr_to_top_of_vtable:
                    offsetToTop = vtables[vptr_to_top_of_vtable[subVTTs[j][i][k]]]['offsetToTop']
                elif subVTTs[j][i][k] in vtables:
                    offsetToTop = vtables[subVTTs[j][i][k]]['offsetToTop']
                if Dword(curVbaseoffsetLoc) + offsetToTop == 0x100000000 or Dword(curVbaseoffsetLoc) + offsetToTop == 0x0:
                    vbaseOffsets[i].append(Dword(curVbaseoffsetLoc))
                    curVbaseoffsetLoc -= DWORD_SIZE
                if vptr > i:
                    if Dword(i) + offsetToTop == 0x100000000 or Dword(i) + offsetToTop == 0x0:
                        vbaseOffsets[i].append(Dword(i))
                        curVbaseoffsetLoc -= DWORD_SIZE
                k += 1

####################End of functions that identify virtual inheritance###########################

#############Start of functions that get distinct bases in virtual inheritance tree####################################
def get_distinct_virtual_bases():
    global parsedInstns, func_vt, ctor_dtor_vt, vbaseOffsets, call_instns, distinctVBases, vptr_to_top_of_vtable, firstVTTWrites
    global vptr_writes
    for v in vbaseOffsets:
        if v in ctor_dtor_vt:
            for cd in ctor_dtor_vt[v]:
                if cd in call_instns:
                    for (ea, callee) in call_instns[cd]:
                        if cd in firstVTTWrites and ea > firstVTTWrites[cd]: continue
                        if in_seg(callee, 'plt'):
                            decode_insn(callee)
                            if cmd.itype == 88: #NN_jmp is 86, but I need 88. I will check the mnemonic for 88
                                if not in_seg(cmd.Operands[0].addr, 'code'):
                                    callee = Dword(cmd.Operands[0].addr)
                                else:
                                    callee = cmd.Operands[0].addr
                        if callee in func_vt and ea in parsedInstns:
                            objAddrs = parsedInstns[ea]
                            for off in objAddrs:
                            	if 7 in objAddrs[off] and off in vbaseOffsets[v]:
                                    if not v in distinctVBases:
                                        distinctVBases[v] = set()
                                    if func_vt[callee] in top_of_vtable_tovptr:
                                        distinctVBases[v].add(top_of_vtable_tovptr[func_vt[callee]])
                                    else:
                                        distinctVBases[v].add(func_vt[callee])
                if cd in vptr_writes:
                    for w in vptr_writes[cd]:
                        if vptr_writes[cd][w]['offset'] in vbaseOffsets[v]:
                            if not v in distinctVBases:
                                distinctVBases[v] = set()
                            distinctVBases[v].add(w)
        elif v in top_of_vtable_tovptr and top_of_vtable_tovptr[v] in ctor_dtor_vt:
            for cd in ctor_dtor_vt[top_of_vtable_tovptr[v]]:
                for (ea, callee) in call_instns[cd]:
                    if cd in firstVTTWrites and ea > firstVTTWrites[cd]: continue
                    if in_seg(callee, 'plt'):
                        decode_insn(callee)
                        if cmd.itype == 88: #NN_jmp is 86, but 88 is needed.
                            if not in_seg(cmd.Operands[0].addr, 'text'):
                                callee = Dword(cmd.Operands[0].addr)
                            else:
                                callee = cmd.Operands[0].addr
                    if callee in func_vt:
                        objAddrs = parsedInstns[ea]
                        for off in objAddrs:
                            if 7 in objAddrs[off] and off in vbaseOffsets[v]:
                                if not v in distinctVBases:
                                    distinctVBases[v] = set()
                                if func_vt[callee] in top_of_vtable_tovptr:
                                    distinctVBases[v].add(top_of_vtable_tovptr[func_vt[callee]])
                                else:
                                    distinctVBases[v].add(func_vt[callee])
                if cd in vptr_writes:
                    for w in vptr_writes[cd]:
                        if vptr_writes[cd][w]['offset'] in vbaseOffsets[v]:
                            if not v in distinctVBases:
                                distinctVBases[v] = set()
                            distinctVBases[v].add(w)

def get_intermediate_bases():
    global list_of_ctor_dtors, VTT_addr_write_instns, func_vt, VTable_hash, hash_to_actual_VTable, intermediate_bases, distinctVBases
    for f in VTT_addr_write_instns:
        if not f in func_vt:
            continue
        vptr = func_vt[f]
        for i in VTT_addr_write_instns[f]:
            if not i in VTTEntrys_To_Vtables: continue
            if VTTEntrys_To_Vtables[i] in vptr_to_top_of_vtable:
                vptr_of_VTT_entry = vptr_to_top_of_vtable[VTTEntrys_To_Vtables[i]]
            else:
                vptr_of_VTT_entry = VTTEntrys_To_Vtables[i]
            if vptr in vptr_to_top_of_vtable and vptr_of_VTT_entry in VTable_hash and VTable_hash[vptr_of_VTT_entry] in hash_to_actual_VTable and vptr_to_top_of_vtable[vptr] == hash_to_actual_VTable[VTable_hash[vptr_of_VTT_entry]]: continue    
            if vptr_of_VTT_entry in VTable_hash and VTable_hash[vptr_of_VTT_entry] in hash_to_actual_VTable:
                if not vptr in intermediate_bases:
                    intermediate_bases[vptr] = set()
                intermediate_bases[vptr].add(hash_to_actual_VTable[VTable_hash[vptr_of_VTT_entry]])

def get_rem_intermediates():
    global subVTTs, vptr_to_top_of_vtable, VTable_hash, hash_to_actual_VTable, intermediate_bases
    for v in subVTTs:
        vptr = Dword(v)
        if vptr in vptr_to_top_of_vtable:
            vptr = vptr_to_top_of_vtable[vptr]
        for each in subVTTs[v]:
            if each == vptr: continue
            if each in VTable_hash and VTable_hash[each] in hash_to_actual_VTable:
                if not vptr in intermediate_bases:
                    intermediate_bases[vptr] = set()
                intermediate_bases[vptr].add(hash_to_actual_VTable[VTable_hash[each]])

def finalize_virtual_inher():
    global intermediate_bases, distinctVBases
    loop_intermediate_bases = copy.deepcopy(intermediate_bases)
    for d in loop_intermediate_bases:
        if d in distinctVBases and len(distinctVBases[d]) == 1:
            for b in loop_intermediate_bases[d]:
                if not b in distinctVBases:
                    distinctVBases[b] = distinctVBases[d]
                if b in intermediate_bases:
                    rem = set(intermediate_bases[b]) - set(intermediate_bases[d])
                    if len(rem) > 0:
                        for r in rem:
                            intermediate_bases[d].add(r)
        if not d in distinctVBases:
            for b in loop_intermediate_bases[d]:
                if b in distinctVBases:
                    distinctVBases[d] = set()
                    for v in distinctVBases[b]:
                        distinctVBases[d].add(v)
#############End of functions that get distinct bases in virtual inheritance tree####################################

def main():
    global all_immediates, vtables, possible_VTT_Entries, VTTs, VTTEntrys_To_Vtables, subVTTs, vbaseOffsets, distinctVBases, subVTTKeys, VTT_addr_write_instns
    global VTable_hash, hash_to_actual_VTable, intermediate_bases, possible_constructorVTables, vtables_names, ctor_vtable_and_unique_VBOs
    global list_of_ctor_dtors

    buildsegmap()
    all_immediates = gatherImmediates()
    verifyVTables()
    scanRodataForVTTs()
    remove_VTTs_identified_as_VTables()
    getSubVTTs()
    recoverAndVerifyVBaseOffsets()
    identify_ctor_dtor()
    parseFuncs()
    assign_vptr_to_ctor_dtor()
    get_distinct_virtual_bases()
    mergeVTables()
    get_intermediate_bases()
    finalize_virtual_inher()
    get_rem_intermediates()
    getVTableNames()
    print('Derived class [Virtual Bases] [Intermediate Bases]')
    for d in distinctVBases:
        if d in intermediate_bases:
            print format(d, 'x'), [format(b, 'x') for b in distinctVBases[d]], [format(i, 'x') for i in intermediate_bases[d]]
        else: 
            print format(d, 'x'), [format(b, 'x') for b in distinctVBases[d]]

if __name__ == "__main__":
	main()