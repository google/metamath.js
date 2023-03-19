include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmgm.mm"
include "cmhm.mm"
include "cmgmhm.mm"
include "mndmgm.mm"
include "anim12i.mm"
include "3simpa.mm"
include "eqid.mm"
include "ismhm.mm"
include "ismgmhm.mm"
include "3imtr4i.mm"

theorem mhmismgmhm
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( F e. ( R MndHom S ) -> F e. ( R MgmHom S ) )

  proof
    cR
    cmnd
    wcel
    #
    cS
    cmnd
    wcel
    #
    wa
    #
    cR
    cbs
    cfv
    #
    cS
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
    cR
    cplusg
    cfv
    #
    co
    cF
    cfv
    @6
    cF
    cfv
    @7
    cF
    cfv
    cS
    cplusg
    cfv
    #
    co
    wceq
    vy
    @3
    wral
    vx
    @3
    wral
    #
    cR
    c0g
    cfv
    #
    cF
    cfv
    cS
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    cR
    cmgm
    wcel
    #
    cS
    cmgm
    wcel
    #
    wa
    #
    @5
    @10
    wa
    #
    wa
    cF
    cR
    cS
    cmhm
    co
    wcel
    cF
    cR
    cS
    cmgmhm
    co
    wcel
    @2
    @17
    @14
    @18
    @0
    @15
    @1
    @16
    cR
    mndmgm
    cS
    mndmgm
    anim12i
    @5
    @10
    @13
    3simpa
    anim12i
    vx
    vy
    @3
    @4
    @8
    @9
    cR
    cS
    cF
    @12
    @11
    @3
    eqid
    #
    @4
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    #
    @11
    eqid
    @12
    eqid
    ismhm
    vx
    vy
    @3
    @4
    @8
    @9
    cR
    cS
    cF
    @19
    @20
    @21
    @22
    ismgmhm
    3imtr4i
end
