include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "c0g.mm"
include "wa.mm"
include "cmap.mm"
include "crab.mm"
include "cmhm.mm"
include "df-mhm.mm"
include "elmpt2cl1.mm"

theorem mhmrcl1
  let cS: class S
  let cT: class T
  let cF: class F
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( F e. ( S MndHom T ) -> S e. Mnd )

  proof
    vs
    vt
    cmnd
    cmnd
    vx
    cv
    #
    vy
    cv
    #
    vs
    cv
    #
    cplusg
    cfv
    co
    vf
    cv
    #
    cfv
    @0
    @3
    cfv
    @1
    @3
    cfv
    vt
    cv
    #
    cplusg
    cfv
    co
    wceq
    vy
    @2
    cbs
    cfv
    #
    wral
    vx
    @5
    wral
    @2
    c0g
    cfv
    @3
    cfv
    @4
    c0g
    cfv
    wceq
    wa
    vf
    @4
    cbs
    cfv
    @5
    cmap
    co
    crab
    cS
    cT
    cmhm
    cF
    vx
    vy
    vt
    vf
    vs
    df-mhm
    elmpt2cl1
end
