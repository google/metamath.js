include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "w3a.mm"
include "cn.mm"
include "cle.mm"
include "cif.mm"
include "c1st.mm"
include "c2nd.mm"
include "wceq.mm"
include "wa.mm"
include "csts.mm"
include "co.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "wss.mm"
include "isstruct.mm"
include "simp2.mm"
include "simp3l.mm"
include "c1.mm"
include "cz.mm"
include "1z.mm"
include "nnge1.mm"
include "eluzuzle.mm"
include "sylancr.mm"
include "elnnuz.mm"
include "syl6ibr.mm"
include "adantld.mm"
include "3ad2ant1.mm"
include "a1d.mm"
include "3imp.mm"
include "3jca.mm"
include "op1stg.mm"
include "breq2d.mm"
include "eqidd.mm"
include "ifbieq12d.mm"
include "3adant3.mm"
include "adantr.mm"
include "cxr.mm"
include "eluz2.mm"
include "zre.mm"
include "rexrd.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "sylbi.mm"
include "adantl.mm"
include "impcom.mm"
include "xrmineq.mm"
include "syl.mm"
include "eqtr2d.mm"
include "3adant2.mm"
include "op2ndg.mm"
include "eqcomd.mm"
include "opeq12d.mm"
include "jca.mm"
include "3exp.mm"
include "pm2.43i.mm"
include "expdcom.mm"
include "setsstruct2.mm"

theorem setsstruct
  let cE: class E
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V


  assert |- ( ( E e. V /\ I e. ( ZZ>= ` M ) /\ G Struct <. M , N >. ) -> ( G sSet <. I , E >. ) Struct <. M , if ( I <_ N , N , I ) >. )

  proof
    cE
    cV
    wcel
    #
    cI
    cM
    cuz
    cfv
    wcel
    #
    cG
    cM
    cN
    cop
    #
    cstr
    wbr
    #
    w3a
    @3
    @0
    cI
    cn
    wcel
    #
    w3a
    #
    cM
    cI
    cN
    cle
    wbr
    #
    cN
    cI
    cif
    #
    cop
    #
    cI
    @2
    c1st
    cfv
    #
    cle
    wbr
    #
    cI
    @9
    cif
    #
    cI
    @2
    c2nd
    cfv
    #
    cle
    wbr
    #
    @12
    cI
    cif
    #
    cop
    wceq
    #
    wa
    #
    cG
    cI
    cE
    cop
    csts
    co
    @8
    cstr
    wbr
    @0
    @1
    @3
    @16
    @3
    @0
    @1
    @16
    @3
    @0
    @1
    wa
    #
    @16
    wi
    #
    @3
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    cG
    c0
    csn
    cdif
    wfun
    #
    cG
    cdm
    cM
    cN
    cfz
    co
    wss
    #
    w3a
    @3
    @18
    wi
    #
    cG
    cM
    cN
    isstruct
    @22
    @23
    @25
    @24
    @22
    @3
    @17
    @16
    @22
    @3
    @17
    w3a
    #
    @5
    @15
    @26
    @3
    @0
    @4
    @22
    @3
    @17
    simp2
    @22
    @3
    @0
    @1
    simp3l
    @22
    @3
    @17
    @4
    @22
    @17
    @4
    wi
    #
    @3
    @19
    @20
    @27
    @21
    @19
    @1
    @4
    @0
    @19
    @1
    cI
    c1
    cuz
    cfv
    wcel
    #
    @4
    @19
    c1
    cz
    wcel
    c1
    cM
    cle
    wbr
    @1
    @28
    wi
    1z
    cM
    nnge1
    cM
    c1
    cI
    eluzuzle
    sylancr
    cI
    elnnuz
    syl6ibr
    adantld
    3ad2ant1
    a1d
    3imp
    3jca
    @26
    cM
    @11
    @7
    @14
    @22
    @17
    cM
    @11
    wceq
    @3
    @22
    @17
    wa
    #
    @11
    cI
    cM
    cle
    wbr
    #
    cI
    cM
    cif
    #
    cM
    @22
    @11
    @31
    wceq
    #
    @17
    @19
    @20
    @32
    @21
    @19
    @20
    wa
    #
    @10
    @30
    cI
    @9
    cI
    cM
    @33
    @9
    cM
    cI
    cle
    cM
    cN
    cn
    cn
    op1stg
    #
    breq2d
    @33
    cI
    eqidd
    #
    @34
    ifbieq12d
    3adant3
    adantr
    @29
    cI
    cxr
    wcel
    #
    cM
    cxr
    wcel
    #
    cM
    cI
    cle
    wbr
    #
    w3a
    #
    @31
    cM
    wceq
    @17
    @22
    @39
    @1
    @22
    @39
    wi
    #
    @0
    @1
    cM
    cz
    wcel
    #
    cI
    cz
    wcel
    #
    @38
    w3a
    #
    @40
    cM
    cI
    eluz2
    @43
    @39
    @22
    @43
    @36
    @37
    @38
    @42
    @41
    @36
    @38
    @42
    cI
    cI
    zre
    rexrd
    3ad2ant2
    @41
    @42
    @37
    @38
    @41
    cM
    cM
    zre
    rexrd
    3ad2ant1
    @41
    @42
    @38
    simp3
    3jca
    a1d
    sylbi
    adantl
    impcom
    cI
    cM
    xrmineq
    syl
    eqtr2d
    3adant2
    @22
    @3
    @7
    @14
    wceq
    #
    @17
    @19
    @20
    @44
    @21
    @33
    @6
    @13
    cN
    cI
    @12
    cI
    @33
    cN
    @12
    cI
    cle
    @33
    @12
    cN
    cM
    cN
    cn
    cn
    op2ndg
    eqcomd
    #
    breq2d
    @45
    @35
    ifbieq12d
    3adant3
    3ad2ant1
    opeq12d
    jca
    3exp
    3ad2ant1
    sylbi
    pm2.43i
    expdcom
    3imp
    cE
    cG
    cI
    cV
    @2
    @8
    setsstruct2
    syl
end
