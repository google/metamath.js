include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cpr.mm"
include "cglb.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "meetval.mm"
include "fveq2d.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "prssi.mm"
include "3adant1.mm"
include "prnzg.mm"
include "3ad2ant2.mm"
include "pmapglb.mm"
include "syl3anc.mm"
include "fveq2.mm"
include "iinxprg.mm"
include "3eqtrd.mm"

theorem pmapmeet
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume pmapmeet.b: |- B = ( Base ` K )
  assume pmapmeet.m: |- ./\ = ( meet ` K )
  assume pmapmeet.a: |- A = ( Atoms ` K )
  assume pmapmeet.p: |- P = ( pmap ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( P ` ( X ./\ Y ) ) = ( ( P ` X ) i^i ( P ` Y ) ) )

  proof
    cK
    chlt
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
    cX
    cY
    c.an
    co
    #
    cP
    cfv
    cX
    cY
    cpr
    #
    cK
    cglb
    cfv
    #
    cfv
    #
    cP
    cfv
    #
    vx
    @5
    vx
    cv
    #
    cP
    cfv
    #
    ciin
    #
    cX
    cP
    cfv
    #
    cY
    cP
    cfv
    #
    cin
    #
    @3
    @4
    @7
    cP
    @3
    @6
    cK
    c.an
    chlt
    cB
    cX
    cY
    cB
    @6
    eqid
    #
    pmapmeet.m
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    meetval
    fveq2d
    @3
    @0
    @5
    cB
    wss
    #
    @5
    c0
    wne
    #
    @8
    @11
    wceq
    @16
    @1
    @2
    @17
    @0
    cX
    cY
    cB
    prssi
    3adant1
    @1
    @0
    @18
    @2
    cX
    cY
    cB
    prnzg
    3ad2ant2
    vx
    cB
    @5
    @6
    cK
    cP
    pmapmeet.b
    @15
    pmapmeet.p
    pmapglb
    syl3anc
    @1
    @2
    @11
    @14
    wceq
    @0
    vx
    cX
    cY
    @10
    @12
    @13
    cB
    cB
    @9
    cX
    cP
    fveq2
    @9
    cY
    cP
    fveq2
    iinxprg
    3adant1
    3eqtrd
end
