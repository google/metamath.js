include "ccomf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "chom.mm"
include "wral.mm"
include "cbs.mm"
include "oveqd.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "eqidd.mm"
include "homfeqbas.mm"
include "comfeq.mm"
include "mpbird.mm"

theorem comfeqd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume comfeqd.1: |- ( ph -> ( comp ` C ) = ( comp ` D ) )
  assume comfeqd.2: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )


  assert |- ( ph -> ( comf ` C ) = ( comf ` D ) )

  proof
    wph
    cC
    ccomf
    cfv
    cD
    ccomf
    cfv
    wceq
    vg
    cv
    #
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    #
    co
    @0
    @1
    @4
    @5
    cD
    cco
    cfv
    #
    co
    #
    co
    wceq
    #
    vg
    @3
    @5
    cC
    chom
    cfv
    #
    co
    #
    wral
    #
    vf
    @2
    @3
    @11
    co
    #
    wral
    #
    vz
    cC
    cbs
    cfv
    #
    wral
    #
    vy
    @16
    wral
    #
    vx
    @16
    wral
    wph
    @18
    vx
    @16
    wph
    @17
    vy
    @16
    wph
    @15
    vz
    @16
    wph
    @13
    vf
    @14
    wph
    @10
    vg
    @12
    wph
    @7
    @9
    @0
    @1
    wph
    @6
    @8
    @4
    @5
    comfeqd.1
    oveqd
    oveqd
    ralrimivw
    ralrimivw
    ralrimivw
    ralrimivw
    ralrimivw
    wph
    vx
    vy
    vz
    @16
    cC
    cD
    @8
    @6
    vf
    vg
    @11
    @6
    eqid
    @8
    eqid
    @11
    eqid
    wph
    @16
    eqidd
    wph
    cC
    cD
    comfeqd.2
    homfeqbas
    comfeqd.2
    comfeq
    mpbird
end
