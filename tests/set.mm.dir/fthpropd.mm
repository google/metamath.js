include "cfth.mm"
include "co.mm"
include "relfth.mm"
include "cv.mm"
include "cfunc.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "cbs.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "funcpropd.mm"
include "breqd.mm"
include "homfeqbas.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "eqid.mm"
include "isfth.mm"
include "3bitr4g.mm"
include "eqbrrdiv.mm"

theorem fthpropd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume fullpropd.1: |- ( ph -> ( Homf ` A ) = ( Homf ` B ) )
  assume fullpropd.2: |- ( ph -> ( comf ` A ) = ( comf ` B ) )
  assume fullpropd.3: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume fullpropd.4: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume fullpropd.a: |- ( ph -> A e. V )
  assume fullpropd.b: |- ( ph -> B e. V )
  assume fullpropd.c: |- ( ph -> C e. V )
  assume fullpropd.d: |- ( ph -> D e. V )


  assert |- ( ph -> ( A Faith C ) = ( B Faith D ) )

  proof
    wph
    vf
    vg
    cA
    cC
    cfth
    co
    #
    cB
    cD
    cfth
    co
    #
    cA
    cC
    relfth
    cB
    cD
    relfth
    wph
    vf
    cv
    #
    vg
    cv
    #
    cA
    cC
    cfunc
    co
    #
    wbr
    #
    vx
    cv
    vy
    cv
    @3
    co
    ccnv
    wfun
    #
    vy
    cA
    cbs
    cfv
    #
    wral
    #
    vx
    @7
    wral
    #
    wa
    @2
    @3
    cB
    cD
    cfunc
    co
    #
    wbr
    #
    @6
    vy
    cB
    cbs
    cfv
    #
    wral
    #
    vx
    @12
    wral
    #
    wa
    @2
    @3
    @0
    wbr
    @2
    @3
    @1
    wbr
    wph
    @5
    @11
    @9
    @14
    wph
    @4
    @10
    @2
    @3
    wph
    cA
    cB
    cC
    cD
    cV
    fullpropd.1
    fullpropd.2
    fullpropd.3
    fullpropd.4
    fullpropd.a
    fullpropd.b
    fullpropd.c
    fullpropd.d
    funcpropd
    breqd
    wph
    @8
    @13
    vx
    @7
    @12
    wph
    cA
    cB
    fullpropd.1
    homfeqbas
    #
    wph
    @6
    vy
    @7
    @12
    @15
    raleqdv
    raleqbidv
    anbi12d
    vx
    vy
    @7
    cA
    cC
    @2
    @3
    @7
    eqid
    isfth
    vx
    vy
    @12
    cB
    cD
    @2
    @3
    @12
    eqid
    isfth
    3bitr4g
    eqbrrdiv
end
