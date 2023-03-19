include "clmod.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "clmhm.mm"
include "co.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "cbs.mm"
include "cfv.mm"
include "cvsca.mm"
include "cof.mm"
include "cgsu.mm"
include "cmpt.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "csca.mm"
include "a1i.mm"
include "simp3.mm"
include "frlmup1.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "ovex.mm"
include "fnmpti.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant1.mm"
include "uvcff.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "frn.mm"
include "fnco.mm"
include "syl3anc.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "fvco2.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "frlmup2.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "cres.mm"
include "ccnv.mm"
include "wi.mm"
include "wral.mm"
include "wfun.mm"
include "ffun.mm"
include "funcoeqres.mm"
include "ex.mm"
include "ralrimivw.mm"
include "clspn.mm"
include "clbs.mm"
include "frlmlbs.mm"
include "lbssp.mm"
include "lspextmo.mm"
include "rmoim.mm"
include "sylc.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem frlmup4
  let cA: class A
  let cC: class C
  let cR: class R
  let cT: class T
  let cU: class U
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume frlmup4.r: |- R = ( Scalar ` T )
  assume frlmup4.f: |- F = ( R freeLMod I )
  assume frlmup4.u: |- U = ( R unitVec I )
  assume frlmup4.c: |- C = ( Base ` T )

  disjoint A m
  disjoint F m
  disjoint T m
  disjoint U m
  disjoint A x
  disjoint m x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint I x
  disjoint I y
  disjoint R x
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  assert |- ( ( T e. LMod /\ I e. X /\ A : I --> C ) -> E! m e. ( F LMHom T ) ( m o. U ) = A )

  proof
    cT
    clmod
    wcel
    #
    cI
    cX
    wcel
    #
    cI
    cC
    cA
    wf
    #
    w3a
    #
    vm
    cv
    #
    cU
    ccom
    #
    cA
    wceq
    #
    vm
    cF
    cT
    clmhm
    co
    #
    wrex
    #
    @6
    vm
    @7
    wrmo
    #
    @6
    vm
    @7
    wreu
    @3
    vx
    cF
    cbs
    cfv
    #
    cT
    vx
    cv
    cA
    cT
    cvsca
    cfv
    #
    cof
    co
    #
    cgsu
    co
    #
    cmpt
    #
    @7
    wcel
    @14
    cU
    ccom
    #
    cA
    wceq
    #
    @8
    @3
    vx
    cA
    @10
    cC
    cR
    cT
    @11
    @14
    cF
    cI
    cX
    frlmup4.f
    @10
    eqid
    #
    frlmup4.c
    @11
    eqid
    #
    @14
    eqid
    #
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    cR
    cT
    csca
    cfv
    wceq
    #
    @3
    frlmup4.r
    a1i
    @0
    @1
    @2
    simp3
    frlmup1
    @3
    vy
    cI
    @15
    cA
    @3
    @14
    @10
    wfn
    #
    cU
    cI
    wfn
    #
    cU
    crn
    #
    @10
    wss
    #
    @15
    cI
    wfn
    @22
    @3
    vx
    @10
    @13
    @14
    cT
    @12
    cgsu
    ovex
    @19
    fnmpti
    a1i
    @3
    cI
    @10
    cU
    wf
    #
    @23
    @3
    cR
    crg
    wcel
    #
    @1
    @26
    @0
    @1
    @27
    @2
    cR
    cT
    frlmup4.r
    lmodring
    3ad2ant1
    #
    @20
    @10
    cR
    cU
    cI
    cX
    cF
    frlmup4.u
    frlmup4.f
    @17
    uvcff
    syl2anc
    #
    cI
    @10
    cU
    ffn
    #
    syl
    @3
    @26
    @25
    @29
    cI
    @10
    cU
    frn
    syl
    #
    @10
    cI
    @14
    cU
    fnco
    syl3anc
    @2
    @0
    cA
    cI
    wfn
    @1
    cI
    cC
    cA
    ffn
    3ad2ant3
    @3
    vy
    cv
    #
    cI
    wcel
    #
    wa
    #
    @32
    @15
    cfv
    #
    @32
    cU
    cfv
    @14
    cfv
    #
    @32
    cA
    cfv
    @34
    @23
    @33
    @35
    @36
    wceq
    @34
    @26
    @23
    @3
    @26
    @33
    @29
    adantr
    @30
    syl
    @3
    @33
    simpr
    #
    cI
    @14
    cU
    @32
    fvco2
    syl2anc
    @34
    vx
    cA
    @10
    cC
    cR
    cT
    @11
    cU
    @14
    cF
    cI
    cX
    @32
    frlmup4.f
    @17
    frlmup4.c
    @18
    @19
    @0
    @1
    @2
    @33
    simpl1
    @0
    @1
    @2
    @33
    simpl2
    @21
    @34
    frlmup4.r
    a1i
    @0
    @1
    @2
    @33
    simpl3
    @37
    frlmup4.u
    frlmup2
    eqtrd
    eqfnfvd
    @6
    @16
    vm
    @14
    @7
    @4
    @14
    wceq
    @5
    @15
    cA
    @4
    @14
    cU
    coeq1
    eqeq1d
    rspcev
    syl2anc
    @3
    @6
    @4
    @24
    cres
    cA
    cU
    ccnv
    ccom
    #
    wceq
    #
    wi
    #
    vm
    @7
    wral
    #
    @39
    vm
    @7
    wrmo
    #
    @9
    @3
    cU
    wfun
    #
    @41
    @3
    @26
    @43
    @29
    cI
    @10
    cU
    ffun
    syl
    @43
    @40
    vm
    @7
    @43
    @6
    @39
    @4
    cU
    cA
    funcoeqres
    ex
    ralrimivw
    syl
    @3
    @25
    @24
    cF
    clspn
    cfv
    #
    cfv
    @10
    wceq
    #
    @42
    @31
    @3
    @24
    cF
    clbs
    cfv
    #
    wcel
    #
    @45
    @3
    @27
    @1
    @47
    @28
    @20
    cR
    cU
    cF
    cI
    @46
    cX
    frlmup4.f
    frlmup4.u
    @46
    eqid
    #
    frlmlbs
    syl2anc
    @24
    @46
    @44
    @10
    cF
    @17
    @48
    @44
    eqid
    #
    lbssp
    syl
    @10
    cF
    cT
    vm
    @38
    @44
    @24
    @17
    @49
    lspextmo
    syl2anc
    @6
    @39
    vm
    @7
    rmoim
    sylc
    @6
    vm
    @7
    reu5
    sylanbrc
end
