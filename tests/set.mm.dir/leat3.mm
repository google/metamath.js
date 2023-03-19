include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "leat.mm"
include "wi.mm"
include "simpl3.mm"
include "eleq1a.mm"
include "syl.mm"
include "orim1d.mm"
include "mpd.mm"

theorem leat3
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume leatom.b: |- B = ( Base ` K )
  assume leatom.l: |- .<_ = ( le ` K )
  assume leatom.z: |- .0. = ( 0. ` K )
  assume leatom.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OP /\ X e. B /\ P e. A ) /\ X .<_ P ) -> ( X e. A \/ X = .0. ) )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    cX
    cP
    c.le
    wbr
    #
    wa
    #
    cX
    cP
    wceq
    #
    cX
    c.0
    wceq
    #
    wo
    cX
    cA
    wcel
    #
    @6
    wo
    cA
    cB
    cP
    cK
    c.le
    cX
    c.0
    leatom.b
    leatom.l
    leatom.z
    leatom.a
    leat
    @4
    @5
    @7
    @6
    @4
    @2
    @5
    @7
    wi
    @0
    @1
    @2
    @3
    simpl3
    cP
    cA
    cX
    eleq1a
    syl
    orim1d
    mpd
end
