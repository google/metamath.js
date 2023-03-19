include "cgr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "grpoidinv.mm"
include "simpll.mm"
include "ralimi.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "adantll.mm"
include "sylan2.mm"
include "grpoidinvlem4.mm"
include "syldan.mm"
include "an32s.mm"
include "adantllr.mm"
include "adantr.mm"
include "ad2ant2rl.mm"
include "ad2ant2lr.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "mpand.mm"
include "ralrimiva.mm"
include "jca.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralbidv.mm"
include "reu8.mm"
include "sylibr.mm"

theorem grpoideu
  let vx: setvar x
  let vu: setvar u
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  assume grpfo.1: |- X = ran G

  disjoint u x
  disjoint G u
  disjoint G x
  disjoint X u
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint U y
  assert |- ( G e. GrpOp -> E! u e. X A. x e. X ( u G x ) = x )

  proof
    cG
    cgr
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    #
    @2
    wceq
    #
    vx
    cX
    wral
    #
    vw
    cv
    #
    @2
    cG
    co
    #
    @2
    wceq
    #
    vx
    cX
    wral
    #
    vu
    vw
    weq
    #
    wi
    #
    vw
    cX
    wral
    #
    wa
    #
    vu
    cX
    wrex
    #
    @5
    vu
    cX
    wreu
    @0
    @1
    vz
    cv
    #
    cG
    co
    #
    @15
    wceq
    #
    @15
    @1
    cG
    co
    @15
    wceq
    #
    wa
    #
    vy
    cv
    #
    @15
    cG
    co
    #
    @1
    wceq
    #
    @15
    @20
    cG
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    wa
    #
    vz
    cX
    wral
    #
    vu
    cX
    wrex
    @14
    vz
    vy
    vu
    cG
    cX
    grpfo.1
    grpoidinv
    @0
    @28
    @13
    vu
    cX
    @0
    @1
    cX
    wcel
    #
    wa
    #
    @28
    @13
    @30
    @28
    wa
    #
    @5
    @12
    @28
    @5
    @30
    @28
    @17
    vz
    cX
    wral
    @5
    @27
    @17
    vz
    cX
    @17
    @18
    @26
    simpll
    ralimi
    @17
    @4
    vz
    vx
    cX
    vz
    vx
    weq
    #
    @16
    @3
    @15
    @2
    @15
    @2
    @1
    cG
    oveq2
    @32
    id
    eqeq12d
    cbvralv
    sylib
    #
    adantl
    @31
    @11
    vw
    cX
    @31
    @6
    cX
    wcel
    #
    wa
    #
    @5
    @9
    @10
    @28
    @5
    @30
    @34
    @33
    ad2antlr
    @35
    @5
    @9
    wa
    #
    @10
    @35
    @36
    wa
    @6
    @1
    cG
    co
    #
    @1
    @6
    cG
    co
    #
    @1
    @6
    @35
    @37
    @38
    wceq
    #
    @36
    @0
    @28
    @34
    @39
    @29
    @0
    @34
    @28
    @39
    @0
    @34
    wa
    #
    @28
    @20
    @6
    cG
    co
    #
    @1
    wceq
    #
    @6
    @20
    cG
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    @39
    @28
    @40
    @26
    vz
    cX
    wral
    #
    @46
    @27
    @26
    vz
    cX
    @19
    @26
    simpr
    ralimi
    @34
    @47
    @46
    @0
    @26
    @46
    vz
    @6
    cX
    vz
    vw
    weq
    #
    @25
    @45
    vy
    cX
    @48
    @22
    @42
    @24
    @44
    @48
    @21
    @41
    @1
    @15
    @6
    @20
    cG
    oveq2
    eqeq1d
    @48
    @23
    @43
    @1
    @15
    @6
    @20
    cG
    oveq1
    eqeq1d
    anbi12d
    rexbidv
    rspcva
    adantll
    sylan2
    vy
    @6
    @1
    cG
    cX
    grpfo.1
    grpoidinvlem4
    syldan
    an32s
    adantllr
    adantr
    @30
    @34
    @36
    @37
    @1
    wceq
    #
    @28
    @30
    @9
    @49
    @34
    @5
    @29
    @9
    @49
    @0
    @8
    @49
    vx
    @1
    cX
    vx
    vu
    weq
    #
    @7
    @37
    @2
    @1
    @2
    @1
    @6
    cG
    oveq2
    @50
    id
    eqeq12d
    rspcva
    adantll
    ad2ant2rl
    adantllr
    @34
    @5
    @38
    @6
    wceq
    #
    @31
    @9
    @4
    @51
    vx
    @6
    cX
    vx
    vw
    weq
    #
    @3
    @38
    @2
    @6
    @2
    @6
    @1
    cG
    oveq2
    @52
    id
    eqeq12d
    rspcva
    ad2ant2lr
    3eqtr3d
    ex
    mpand
    ralrimiva
    jca
    ex
    reximdva
    mpd
    @5
    @9
    vu
    vw
    cX
    @10
    @4
    @8
    vx
    cX
    @10
    @3
    @7
    @2
    @1
    @6
    @2
    cG
    oveq1
    eqeq1d
    ralbidv
    reu8
    sylibr
end
