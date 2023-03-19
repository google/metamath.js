include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cif.mm"
include "cop.mm"
include "cmpt2.mm"
include "ccom.mm"
include "csmat.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "3ad2ant3.mm"
include "coeq1.mm"
include "mpt2eq3dv.mm"
include "df-smat.mm"
include "nnex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wa.mm"
include "breq2.mm"
include "ifbid.mm"
include "opeq1d.mm"
include "opeq2d.mm"
include "sylan9eq.mm"
include "adantl.mm"
include "coeq2d.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "a1i.mm"
include "coexg.mm"
include "syl2anc.mm"
include "ovmpt2d.mm"

theorem smatfval
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cL: class L
  let cM: class M
  let cV: class V
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m

  disjoint K i
  disjoint K j
  disjoint i j
  disjoint L i
  disjoint L j
  disjoint K k
  disjoint K l
  disjoint K m
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint L k
  disjoint L l
  disjoint M k
  disjoint M l
  disjoint M m
  disjoint V k
  disjoint V l
  assert |- ( ( K e. NN /\ L e. NN /\ M e. V ) -> ( K ( subMat1 ` M ) L ) = ( M o. ( i e. NN , j e. NN |-> <. if ( i < K , i , ( i + 1 ) ) , if ( j < L , j , ( j + 1 ) ) >. ) ) )

  proof
    cK
    cn
    wcel
    #
    cL
    cn
    wcel
    #
    cM
    cV
    wcel
    #
    w3a
    #
    vk
    vl
    cK
    cL
    cn
    cn
    cM
    vi
    vj
    cn
    cn
    vi
    cv
    #
    vk
    cv
    #
    clt
    wbr
    #
    @4
    @4
    c1
    caddc
    co
    #
    cif
    #
    vj
    cv
    #
    vl
    cv
    #
    clt
    wbr
    #
    @9
    @9
    c1
    caddc
    co
    #
    cif
    #
    cop
    #
    cmpt2
    #
    ccom
    #
    cM
    vi
    vj
    cn
    cn
    @4
    cK
    clt
    wbr
    #
    @4
    @7
    cif
    #
    @9
    cL
    clt
    wbr
    #
    @9
    @12
    cif
    #
    cop
    #
    cmpt2
    #
    ccom
    #
    cM
    csmat
    cfv
    #
    cvv
    @3
    cM
    cvv
    wcel
    #
    @24
    vk
    vl
    cn
    cn
    @16
    cmpt2
    #
    wceq
    @2
    @0
    @25
    @1
    cM
    cV
    elex
    3ad2ant3
    vm
    cM
    vk
    vl
    cn
    cn
    vm
    cv
    #
    @15
    ccom
    #
    cmpt2
    @26
    cvv
    csmat
    @27
    cM
    wceq
    vk
    vl
    cn
    cn
    @28
    @16
    @27
    cM
    @15
    coeq1
    mpt2eq3dv
    vi
    vj
    vk
    vm
    vl
    df-smat
    vk
    vl
    cn
    cn
    @16
    nnex
    nnex
    mpt2ex
    fvmpt
    syl
    @3
    @5
    cK
    wceq
    #
    @10
    cL
    wceq
    #
    wa
    #
    wa
    @15
    @22
    cM
    @31
    @15
    @22
    wceq
    @3
    @29
    @30
    @15
    vi
    vj
    cn
    cn
    @18
    @13
    cop
    #
    cmpt2
    @22
    @29
    vi
    vj
    cn
    cn
    @14
    @32
    @29
    @8
    @18
    @13
    @29
    @6
    @17
    @4
    @7
    @5
    cK
    @4
    clt
    breq2
    ifbid
    opeq1d
    mpt2eq3dv
    @30
    vi
    vj
    cn
    cn
    @32
    @21
    @30
    @13
    @20
    @18
    @30
    @11
    @19
    @9
    @12
    @10
    cL
    @9
    clt
    breq2
    ifbid
    opeq2d
    mpt2eq3dv
    sylan9eq
    adantl
    coeq2d
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @3
    @2
    @22
    cvv
    wcel
    #
    @23
    cvv
    wcel
    @0
    @1
    @2
    simp3
    @33
    @3
    vi
    vj
    cn
    cn
    @21
    nnex
    nnex
    mpt2ex
    a1i
    cM
    @22
    cV
    cvv
    coexg
    syl2anc
    ovmpt2d
end
