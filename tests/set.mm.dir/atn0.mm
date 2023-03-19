include "cal.mm"
include "wcel.mm"
include "wne.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "isat3.mm"
include "simp2.mm"
include "syl6bi.mm"
include "imp.mm"

theorem atn0
  let cA: class A
  let cP: class P
  let cK: class K
  let c.0: class .0.
  let vx: setvar x
  assume atne0.z: |- .0. = ( 0. ` K )
  assume atne0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A ) -> P =/= .0. )

  proof
    cK
    cal
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    c.0
    wne
    #
    @0
    @1
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    vx
    cv
    #
    cP
    cK
    cple
    cfv
    #
    wbr
    @5
    cP
    wceq
    @5
    c.0
    wceq
    wo
    wi
    vx
    @3
    wral
    #
    w3a
    @2
    vx
    cA
    @3
    cP
    cK
    @6
    c.0
    @3
    eqid
    @6
    eqid
    atne0.z
    atne0.a
    isat3
    @4
    @2
    @7
    simp2
    syl6bi
    imp
end
