include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "elpadd0.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem paddval0
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cS: class S
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. B /\ X C_ A /\ Y C_ A ) /\ -. ( X =/= (/) /\ Y =/= (/) ) ) -> ( X .+ Y ) = ( X u. Y ) )

  proof
    cK
    cB
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    cX
    c0
    wne
    cY
    c0
    wne
    wa
    wn
    wa
    #
    vq
    cX
    cY
    c.pl
    co
    #
    cX
    cY
    cun
    #
    @0
    vq
    cv
    #
    @1
    wcel
    @3
    cX
    wcel
    @3
    cY
    wcel
    wo
    @3
    @2
    wcel
    cA
    cB
    c.pl
    @3
    cK
    cX
    cY
    padd0.a
    padd0.p
    elpadd0
    @3
    cX
    cY
    elun
    syl6bbr
    eqrdv
end
