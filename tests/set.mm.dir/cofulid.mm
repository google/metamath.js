include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "cbs.mm"
include "cv.mm"
include "c2nd.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "ccofu.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "cfunc.mm"
include "wa.mm"
include "funcrcl.mm"
include "syl.mm"
include "simprd.mm"
include "idfu1st.mm"
include "coeq1d.mm"
include "wf.mm"
include "wceq.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fcoi2.mm"
include "eqtrd.mm"
include "w3a.mm"
include "chom.mm"
include "3ad2ant1.mm"
include "ffvelrnda.mm"
include "3adant3.mm"
include "3adant2.mm"
include "idfu2nd.mm"
include "simp2.mm"
include "simp3.mm"
include "funcf2.mm"
include "mpt2eq3dva.mm"
include "cxp.mm"
include "wfn.mm"
include "funcfn2.mm"
include "fnov.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "opeq12d.mm"
include "idfucl.mm"
include "cofuval.mm"
include "1st2nd.mm"
include "3eqtr4d.mm"

theorem cofulid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cF: class F
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume cofulid.g: |- ( ph -> F e. ( C Func D ) )
  assume cofulid.1: |- I = ( idFunc ` D )


  assert |- ( ph -> ( I o.func F ) = F )

  proof
    wph
    cI
    c1st
    cfv
    #
    cF
    c1st
    cfv
    #
    ccom
    #
    vx
    vy
    cC
    cbs
    cfv
    #
    @3
    vx
    cv
    #
    @1
    cfv
    #
    vy
    cv
    #
    @1
    cfv
    #
    cI
    c2nd
    cfv
    co
    #
    @4
    @6
    cF
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    @1
    @9
    cop
    #
    cI
    cF
    ccofu
    co
    cF
    wph
    @2
    @1
    @12
    @9
    wph
    @2
    cid
    cD
    cbs
    cfv
    #
    cres
    #
    @1
    ccom
    #
    @1
    wph
    @0
    @15
    @1
    wph
    @14
    cD
    cI
    cofulid.1
    @14
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    wph
    cF
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    @18
    @19
    wa
    cofulid.g
    cC
    cD
    cF
    funcrcl
    syl
    simprd
    #
    idfu1st
    coeq1d
    wph
    @3
    @14
    @1
    wf
    @16
    @1
    wceq
    wph
    @3
    @14
    cC
    cD
    @1
    @9
    @3
    eqid
    #
    @17
    wph
    @20
    wrel
    #
    @21
    @1
    @9
    @20
    wbr
    #
    cC
    cD
    relfunc
    #
    cofulid.g
    cF
    @20
    1st2ndbr
    sylancr
    #
    funcf1
    #
    @3
    @14
    @1
    fcoi2
    syl
    eqtrd
    wph
    @12
    vx
    vy
    @3
    @3
    @10
    cmpt2
    #
    @9
    wph
    vx
    vy
    @3
    @3
    @11
    @10
    wph
    @4
    @3
    wcel
    #
    @6
    @3
    wcel
    #
    w3a
    #
    @11
    cid
    @5
    @7
    cD
    chom
    cfv
    #
    co
    #
    cres
    #
    @10
    ccom
    #
    @10
    @32
    @8
    @35
    @10
    @32
    @14
    cD
    @33
    cI
    @5
    @7
    cofulid.1
    @17
    wph
    @30
    @19
    @31
    @22
    3ad2ant1
    @33
    eqid
    #
    wph
    @30
    @5
    @14
    wcel
    @31
    wph
    @3
    @14
    @4
    @1
    @28
    ffvelrnda
    3adant3
    wph
    @31
    @7
    @14
    wcel
    @30
    wph
    @3
    @14
    @6
    @1
    @28
    ffvelrnda
    3adant2
    idfu2nd
    coeq1d
    @32
    @4
    @6
    cC
    chom
    cfv
    #
    co
    #
    @34
    @10
    wf
    @36
    @10
    wceq
    @32
    @3
    cC
    cD
    @1
    @9
    @38
    @33
    @4
    @6
    @23
    @38
    eqid
    @37
    wph
    @30
    @25
    @31
    @27
    3ad2ant1
    wph
    @30
    @31
    simp2
    wph
    @30
    @31
    simp3
    funcf2
    @39
    @34
    @10
    fcoi2
    syl
    eqtrd
    mpt2eq3dva
    wph
    @9
    @3
    @3
    cxp
    wfn
    @9
    @29
    wceq
    wph
    @3
    cC
    cD
    @1
    @9
    @23
    @27
    funcfn2
    vx
    vy
    @3
    @3
    @9
    fnov
    sylib
    eqtr4d
    opeq12d
    wph
    vx
    vy
    @3
    cC
    cD
    cD
    cF
    cI
    @23
    cofulid.g
    wph
    @19
    cI
    cD
    cD
    cfunc
    co
    wcel
    @22
    cD
    cI
    cofulid.1
    idfucl
    syl
    cofuval
    wph
    @24
    @21
    cF
    @13
    wceq
    @26
    cofulid.g
    cF
    @20
    1st2nd
    sylancr
    3eqtr4d
end
