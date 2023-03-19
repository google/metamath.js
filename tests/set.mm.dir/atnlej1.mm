include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "latnlej1l.mm"
include "syl131anc.mm"

theorem atnlej1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume atnlej.l: |- .<_ = ( le ` K )
  assume atnlej.j: |- .\/ = ( join ` K )
  assume atnlej.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ -. P .<_ ( Q .\/ R ) ) -> P =/= Q )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
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
    cP
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @8
    wcel
    #
    cR
    @8
    wcel
    #
    @5
    cP
    cQ
    wne
    @0
    @4
    @7
    @5
    cK
    hllat
    3ad2ant1
    @6
    @1
    @9
    @0
    @1
    @2
    @3
    @5
    simp21
    cA
    @8
    cP
    cK
    @8
    eqid
    #
    atnlej.a
    atbase
    syl
    @6
    @2
    @10
    @0
    @1
    @2
    @3
    @5
    simp22
    cA
    @8
    cQ
    cK
    @12
    atnlej.a
    atbase
    syl
    @6
    @3
    @11
    @0
    @1
    @2
    @3
    @5
    simp23
    cA
    @8
    cR
    cK
    @12
    atnlej.a
    atbase
    syl
    @0
    @4
    @5
    simp3
    @8
    c.or
    cK
    c.le
    cP
    cQ
    cR
    @12
    atnlej.l
    atnlej.j
    latnlej1l
    syl131anc
end
