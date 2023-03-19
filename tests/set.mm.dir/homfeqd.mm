include "chomf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "cbs.mm"
include "wral.mm"
include "oveqd.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "eqidd.mm"
include "homfeq.mm"
include "mpbird.mm"

theorem homfeqd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume homfeqd.1: |- ( ph -> ( Base ` C ) = ( Base ` D ) )
  assume homfeqd.2: |- ( ph -> ( Hom ` C ) = ( Hom ` D ) )


  assert |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )

  proof
    wph
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    vx
    cv
    #
    vy
    cv
    #
    cC
    chom
    cfv
    #
    co
    @0
    @1
    cD
    chom
    cfv
    #
    co
    wceq
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    #
    vx
    @5
    wral
    wph
    @6
    vx
    @5
    wph
    @4
    vy
    @5
    wph
    @2
    @3
    @0
    @1
    homfeqd.2
    oveqd
    ralrimivw
    ralrimivw
    wph
    vx
    vy
    @5
    cC
    cD
    @2
    @3
    @2
    eqid
    @3
    eqid
    wph
    @5
    eqidd
    homfeqd.1
    homfeq
    mpbird
end
