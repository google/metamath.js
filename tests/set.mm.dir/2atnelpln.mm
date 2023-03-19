include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "latref.mm"
include "syl2anc.mm"
include "wn.mm"
include "wa.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "lplnnle2at.mm"
include "syl13anc.mm"
include "ex.mm"
include "mt2d.mm"

theorem 2atnelpln
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume 2atnelpln.j: |- .\/ = ( join ` K )
  assume 2atnelpln.a: |- A = ( Atoms ` K )
  assume 2atnelpln.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ Q e. A /\ R e. A ) -> -. ( Q .\/ R ) e. P )

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
    w3a
    #
    cQ
    cR
    c.or
    co
    #
    cP
    wcel
    #
    @4
    @4
    cK
    cple
    cfv
    #
    wbr
    #
    @3
    cK
    clat
    wcel
    #
    @4
    cK
    cbs
    cfv
    #
    wcel
    @7
    @0
    @1
    @8
    @2
    cK
    hllat
    3ad2ant1
    cA
    @9
    c.or
    cK
    cQ
    cR
    @9
    eqid
    #
    2atnelpln.j
    2atnelpln.a
    hlatjcl
    @9
    cK
    @6
    @4
    @10
    @6
    eqid
    #
    latref
    syl2anc
    @3
    @5
    @7
    wn
    #
    @3
    @5
    wa
    @0
    @5
    @1
    @2
    @12
    @0
    @1
    @2
    @5
    simpl1
    @3
    @5
    simpr
    @0
    @1
    @2
    @5
    simpl2
    @0
    @1
    @2
    @5
    simpl3
    cA
    cP
    cQ
    cR
    c.or
    cK
    @6
    @4
    @11
    2atnelpln.j
    2atnelpln.a
    2atnelpln.p
    lplnnle2at
    syl13anc
    ex
    mt2d
end
