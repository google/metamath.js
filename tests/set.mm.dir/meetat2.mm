include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "meetat.mm"
include "wi.mm"
include "eleq1a.mm"
include "3ad2ant3.mm"
include "orim1d.mm"
include "mpd.mm"

theorem meetat2
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume m.b: |- B = ( Base ` K )
  assume m.m: |- ./\ = ( meet ` K )
  assume m.z: |- .0. = ( 0. ` K )
  assume m.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. OL /\ X e. B /\ P e. A ) -> ( ( X ./\ P ) e. A \/ ( X ./\ P ) = .0. ) )

  proof
    cK
    col
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
    #
    cX
    cP
    c.an
    co
    #
    cP
    wceq
    #
    @4
    c.0
    wceq
    #
    wo
    @4
    cA
    wcel
    #
    @6
    wo
    cA
    cB
    cP
    cK
    c.an
    cX
    c.0
    m.b
    m.m
    m.z
    m.a
    meetat
    @3
    @5
    @7
    @6
    @2
    @0
    @5
    @7
    wi
    @1
    cP
    cA
    @4
    eleq1a
    3ad2ant3
    orim1d
    mpd
end
