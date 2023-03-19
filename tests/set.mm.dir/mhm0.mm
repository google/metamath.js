include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "cmnd.mm"
include "wa.mm"
include "w3a.mm"
include "eqid.mm"
include "ismhm.mm"
include "simprbi.mm"
include "simp3d.mm"

theorem mhm0
  let cS: class S
  let cT: class T
  let cF: class F
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume mhm0.z: |- .0. = ( 0g ` S )
  assume mhm0.y: |- Y = ( 0g ` T )


  assert |- ( F e. ( S MndHom T ) -> ( F ` .0. ) = Y )

  proof
    cF
    cS
    cT
    cmhm
    co
    wcel
    #
    cS
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    cF
    cfv
    @4
    cF
    cfv
    @5
    cF
    cfv
    cT
    cplusg
    cfv
    #
    co
    wceq
    vy
    @1
    wral
    vx
    @1
    wral
    #
    c.0
    cF
    cfv
    cY
    wceq
    #
    @0
    cS
    cmnd
    wcel
    cT
    cmnd
    wcel
    wa
    @3
    @8
    @9
    w3a
    vx
    vy
    @1
    @2
    @6
    @7
    cS
    cT
    cF
    cY
    c.0
    @1
    eqid
    @2
    eqid
    @6
    eqid
    @7
    eqid
    mhm0.z
    mhm0.y
    ismhm
    simprbi
    simp3d
end
