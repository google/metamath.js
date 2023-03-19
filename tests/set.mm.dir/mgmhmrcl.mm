include "cmgm.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "cmgmhm.mm"
include "df-mgmhm.mm"
include "elmpt2cl.mm"

theorem mgmhmrcl
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( F e. ( S MgmHom T ) -> ( S e. Mgm /\ T e. Mgm ) )

  proof
    vs
    vt
    cmgm
    cmgm
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
    cmgmhm
    cF
    vx
    vy
    vt
    vf
    vs
    df-mgmhm
    elmpt2cl
end
