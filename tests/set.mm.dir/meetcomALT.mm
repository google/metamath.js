include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cglb.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "prcom.mm"
include "fveq2i.mm"
include "a1i.mm"
include "eqid.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "meetval.mm"
include "3eqtr4rd.mm"

theorem meetcomALT
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let cY: class Y
  assume meetcom.b: |- B = ( Base ` K )
  assume meetcom.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. V /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) = ( Y ./\ X ) )

  proof
    cK
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cY
    cX
    cpr
    #
    cK
    cglb
    cfv
    #
    cfv
    #
    cX
    cY
    cpr
    #
    @5
    cfv
    #
    cY
    cX
    c.an
    co
    cX
    cY
    c.an
    co
    @6
    @8
    wceq
    @3
    @4
    @7
    @5
    cY
    cX
    prcom
    fveq2i
    a1i
    @3
    @5
    cK
    c.an
    cV
    cB
    cY
    cX
    cB
    @5
    eqid
    #
    meetcom.m
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp2
    #
    meetval
    @3
    @5
    cK
    c.an
    cV
    cB
    cX
    cY
    cB
    @9
    meetcom.m
    @10
    @12
    @11
    meetval
    3eqtr4rd
end
