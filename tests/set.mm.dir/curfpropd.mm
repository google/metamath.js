include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "co.mm"
include "cmpt.mm"
include "chom.mm"
include "ccid.mm"
include "cop.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "ccurf.mm"
include "homfeqbas.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "adantr.mm"
include "mpteq1d.mm"
include "eqid.mm"
include "chomf.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "homfeqval.mm"
include "ccat.mm"
include "cidpropd.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "mpt2eq123dva.mm"
include "opeq12d.mm"
include "mpteq12dva.mm"
include "ad3antrrr.mm"
include "oveq2d.mm"
include "curfval.mm"
include "cxpc.mm"
include "cfunc.mm"
include "xpcpropd.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"

theorem curfpropd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume curfpropd.1: |- ( ph -> ( Homf ` A ) = ( Homf ` B ) )
  assume curfpropd.2: |- ( ph -> ( comf ` A ) = ( comf ` B ) )
  assume curfpropd.3: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume curfpropd.4: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume curfpropd.a: |- ( ph -> A e. Cat )
  assume curfpropd.b: |- ( ph -> B e. Cat )
  assume curfpropd.c: |- ( ph -> C e. Cat )
  assume curfpropd.d: |- ( ph -> D e. Cat )
  assume curfpropd.f: |- ( ph -> F e. ( ( A Xc. C ) Func E ) )


  assert |- ( ph -> ( <. A , C >. curryF F ) = ( <. B , D >. curryF F ) )

  proof
    wph
    vx
    cA
    cbs
    cfv
    #
    vy
    cC
    cbs
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    c1st
    cfv
    co
    #
    cmpt
    #
    vy
    vz
    @1
    @1
    vg
    @3
    vz
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    @2
    cA
    ccid
    cfv
    #
    cfv
    #
    vg
    cv
    #
    @2
    @3
    cop
    @2
    @6
    cop
    #
    cF
    c2nd
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    cmpt
    #
    vx
    vy
    @0
    @0
    vg
    @2
    @3
    cA
    chom
    cfv
    #
    co
    #
    vz
    @1
    @11
    @6
    cC
    ccid
    cfv
    #
    cfv
    #
    @12
    @3
    @6
    cop
    @13
    co
    #
    co
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    #
    cop
    vx
    cB
    cbs
    cfv
    #
    vy
    cD
    cbs
    cfv
    #
    @4
    cmpt
    #
    vy
    vz
    @30
    @30
    vg
    @3
    @6
    cD
    chom
    cfv
    #
    co
    #
    @2
    cB
    ccid
    cfv
    #
    cfv
    #
    @11
    @14
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    cmpt
    #
    vx
    vy
    @29
    @29
    vg
    @2
    @3
    cB
    chom
    cfv
    #
    co
    #
    vz
    @30
    @11
    @6
    cD
    ccid
    cfv
    #
    cfv
    #
    @24
    co
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    #
    cop
    cA
    cC
    cop
    cF
    ccurf
    co
    #
    cB
    cD
    cop
    cF
    ccurf
    co
    #
    wph
    @19
    @40
    @28
    @48
    wph
    vx
    @0
    @18
    @29
    @39
    wph
    cA
    cB
    curfpropd.1
    homfeqbas
    #
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @5
    @31
    @17
    @38
    @53
    vy
    @1
    @30
    @4
    wph
    @1
    @30
    wceq
    #
    @52
    wph
    cC
    cD
    curfpropd.3
    homfeqbas
    #
    adantr
    #
    mpteq1d
    @53
    vy
    vz
    @1
    @1
    @16
    @30
    @30
    @37
    @56
    @53
    @54
    @3
    @1
    wcel
    #
    @56
    adantr
    @53
    @57
    @6
    @1
    wcel
    #
    wa
    #
    wa
    #
    vg
    @8
    @15
    @33
    @36
    @60
    @1
    cC
    cD
    @7
    @32
    @3
    @6
    @1
    eqid
    #
    @7
    eqid
    #
    @32
    eqid
    #
    wph
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    @52
    @59
    curfpropd.3
    ad2antrr
    @53
    @57
    @58
    simprl
    @53
    @57
    @58
    simprr
    homfeqval
    @60
    @10
    @35
    @11
    @14
    @60
    @2
    @9
    @34
    wph
    @9
    @34
    wceq
    @52
    @59
    wph
    cA
    cB
    ccat
    ccat
    curfpropd.1
    curfpropd.2
    curfpropd.a
    curfpropd.b
    cidpropd
    ad2antrr
    fveq1d
    oveq1d
    mpteq12dv
    mpt2eq123dva
    opeq12d
    mpteq12dva
    wph
    vx
    vy
    @0
    @0
    @27
    @29
    @29
    @47
    @51
    wph
    @0
    @29
    wceq
    @52
    @51
    adantr
    wph
    @52
    @3
    @0
    wcel
    #
    wa
    #
    wa
    #
    vg
    @21
    @26
    @42
    @46
    @66
    @0
    cA
    cB
    @20
    @41
    @2
    @3
    @0
    eqid
    #
    @20
    eqid
    #
    @41
    eqid
    #
    wph
    cA
    chomf
    cfv
    cB
    chomf
    cfv
    wceq
    @65
    curfpropd.1
    adantr
    wph
    @52
    @64
    simprl
    wph
    @52
    @64
    simprr
    homfeqval
    @66
    @11
    @21
    wcel
    #
    wa
    #
    vz
    @1
    @25
    @30
    @45
    wph
    @54
    @65
    @70
    @55
    ad2antrr
    @71
    @58
    wa
    #
    @23
    @44
    @11
    @24
    @72
    @6
    @22
    @43
    wph
    @22
    @43
    wceq
    @65
    @70
    @58
    wph
    cC
    cD
    ccat
    ccat
    curfpropd.3
    curfpropd.4
    curfpropd.c
    curfpropd.d
    cidpropd
    ad3antrrr
    fveq1d
    oveq2d
    mpteq12dva
    mpteq12dva
    mpt2eq123dva
    opeq12d
    wph
    vx
    vy
    vz
    @0
    @1
    cA
    cC
    @9
    vg
    cE
    cF
    @49
    @20
    @22
    @7
    @49
    eqid
    @67
    curfpropd.a
    curfpropd.c
    curfpropd.f
    @61
    @62
    @9
    eqid
    @68
    @22
    eqid
    curfval
    wph
    vx
    vy
    vz
    @29
    @30
    cB
    cD
    @34
    vg
    cE
    cF
    @50
    @41
    @43
    @32
    @50
    eqid
    @29
    eqid
    curfpropd.b
    curfpropd.d
    wph
    cF
    cA
    cC
    cxpc
    co
    #
    cE
    cfunc
    co
    cB
    cD
    cxpc
    co
    #
    cE
    cfunc
    co
    curfpropd.f
    wph
    @73
    @74
    cE
    cfunc
    wph
    cA
    cB
    cC
    cD
    ccat
    curfpropd.1
    curfpropd.2
    curfpropd.3
    curfpropd.4
    curfpropd.a
    curfpropd.b
    curfpropd.c
    curfpropd.d
    xpcpropd
    oveq1d
    eleqtrd
    @30
    eqid
    @63
    @34
    eqid
    @69
    @43
    eqid
    curfval
    3eqtr4d
end
