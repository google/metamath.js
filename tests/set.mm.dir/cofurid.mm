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
include "simpld.mm"
include "idfu1st.mm"
include "coeq2d.mm"
include "wf.mm"
include "wceq.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fcoi1.mm"
include "eqtrd.mm"
include "w3a.mm"
include "chom.mm"
include "3ad2ant1.mm"
include "fveq1d.mm"
include "fvresi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "oveq12d.mm"
include "simp2.mm"
include "simp3.mm"
include "idfu2nd.mm"
include "coeq12d.mm"
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

theorem cofurid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cF: class F
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume cofulid.g: |- ( ph -> F e. ( C Func D ) )
  assume cofurid.1: |- I = ( idFunc ` C )


  assert |- ( ph -> ( F o.func I ) = F )

  proof
    wph
    cF
    c1st
    cfv
    #
    cI
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
    cF
    c2nd
    cfv
    #
    co
    #
    @4
    @6
    cI
    c2nd
    cfv
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    @0
    @8
    cop
    #
    cF
    cI
    ccofu
    co
    cF
    wph
    @2
    @0
    @12
    @8
    wph
    @2
    @0
    cid
    @3
    cres
    #
    ccom
    #
    @0
    wph
    @1
    @14
    @0
    wph
    @3
    cC
    cI
    cofurid.1
    @3
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
    @17
    @18
    wa
    cofulid.g
    cC
    cD
    cF
    funcrcl
    syl
    simpld
    #
    idfu1st
    #
    coeq2d
    wph
    @3
    cD
    cbs
    cfv
    #
    @0
    wf
    @15
    @0
    wceq
    wph
    @3
    @23
    cC
    cD
    @0
    @8
    @16
    @23
    eqid
    wph
    @19
    wrel
    #
    @20
    @0
    @8
    @19
    wbr
    #
    cC
    cD
    relfunc
    #
    cofulid.g
    cF
    @19
    1st2ndbr
    sylancr
    #
    funcf1
    @3
    @23
    @0
    fcoi1
    syl
    eqtrd
    wph
    @12
    vx
    vy
    @3
    @3
    @4
    @6
    @8
    co
    #
    cmpt2
    #
    @8
    wph
    vx
    vy
    @3
    @3
    @11
    @28
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
    @28
    cid
    @4
    @6
    cC
    chom
    cfv
    #
    co
    #
    cres
    #
    ccom
    #
    @28
    @32
    @9
    @28
    @10
    @35
    @32
    @5
    @4
    @7
    @6
    @8
    @32
    @5
    @4
    @14
    cfv
    #
    @4
    @32
    @4
    @1
    @14
    wph
    @30
    @1
    @14
    wceq
    @31
    @22
    3ad2ant1
    #
    fveq1d
    @30
    wph
    @37
    @4
    wceq
    @31
    @3
    @4
    fvresi
    3ad2ant2
    eqtrd
    @32
    @7
    @6
    @14
    cfv
    #
    @6
    @32
    @6
    @1
    @14
    @38
    fveq1d
    @31
    wph
    @39
    @6
    wceq
    @30
    @3
    @6
    fvresi
    3ad2ant3
    eqtrd
    oveq12d
    @32
    @3
    cC
    @33
    cI
    @4
    @6
    cofurid.1
    @16
    wph
    @30
    @17
    @31
    @21
    3ad2ant1
    @33
    eqid
    #
    wph
    @30
    @31
    simp2
    #
    wph
    @30
    @31
    simp3
    #
    idfu2nd
    coeq12d
    @32
    @34
    @4
    @0
    cfv
    @6
    @0
    cfv
    cD
    chom
    cfv
    #
    co
    #
    @28
    wf
    @36
    @28
    wceq
    @32
    @3
    cC
    cD
    @0
    @8
    @33
    @43
    @4
    @6
    @16
    @40
    @43
    eqid
    wph
    @30
    @25
    @31
    @27
    3ad2ant1
    @41
    @42
    funcf2
    @34
    @44
    @28
    fcoi1
    syl
    eqtrd
    mpt2eq3dva
    wph
    @8
    @3
    @3
    cxp
    wfn
    @8
    @29
    wceq
    wph
    @3
    cC
    cD
    @0
    @8
    @16
    @27
    funcfn2
    vx
    vy
    @3
    @3
    @8
    fnov
    sylib
    eqtr4d
    opeq12d
    wph
    vx
    vy
    @3
    cC
    cC
    cD
    cI
    cF
    @16
    wph
    @17
    cI
    cC
    cC
    cfunc
    co
    wcel
    @21
    cC
    cI
    cofurid.1
    idfucl
    syl
    cofulid.g
    cofuval
    wph
    @24
    @20
    cF
    @13
    wceq
    @26
    cofulid.g
    cF
    @19
    1st2nd
    sylancr
    3eqtr4d
end
