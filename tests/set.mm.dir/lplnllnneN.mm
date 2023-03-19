include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "eqid.mm"
include "lplnriaN.mm"
include "wceq.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl23.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "simpr.mm"
include "breqtrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem lplnllnneN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let cY: class Y
  assume lplnri1.j: |- .\/ = ( join ` K )
  assume lplnri1.a: |- A = ( Atoms ` K )
  assume lplnri1.p: |- P = ( LPlanes ` K )
  assume lplnri1.y: |- Y = ( ( Q .\/ R ) .\/ S )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> ( Q .\/ S ) =/= ( R .\/ S ) )

  proof
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    w3a
    #
    cY
    cP
    wcel
    #
    w3a
    #
    cQ
    cR
    cS
    c.or
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    cQ
    cS
    c.or
    co
    #
    @7
    wne
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    @8
    cY
    @8
    eqid
    #
    lplnri1.j
    lplnri1.a
    lplnri1.p
    lplnri1.y
    lplnriaN
    @6
    @9
    @10
    @7
    @6
    @10
    @7
    wceq
    #
    @9
    @6
    @12
    wa
    #
    cQ
    @10
    @7
    @8
    @13
    @0
    @1
    @3
    cQ
    @10
    @8
    wbr
    @0
    @4
    @5
    @12
    simpl1
    @1
    @2
    @3
    @0
    @5
    @12
    simpl21
    @1
    @2
    @3
    @0
    @5
    @12
    simpl23
    cA
    cQ
    cS
    c.or
    cK
    @8
    @11
    lplnri1.j
    lplnri1.a
    hlatlej1
    syl3anc
    @6
    @12
    simpr
    breqtrd
    ex
    necon3bd
    mpd
end
