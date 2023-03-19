include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp23.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3r.mm"
include "latnlej1r.mm"
include "syl131anc.mm"
include "necomd.mm"
include "wi.mm"
include "simp1.mm"
include "simp3l.mm"
include "hlatexch1.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "mtod.mm"
include "jca.mm"

theorem 3noncolr2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3noncol.l: |- .<_ = ( le ` K )
  assume 3noncol.j: |- .\/ = ( join ` K )
  assume 3noncol.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> ( Q =/= R /\ -. P .<_ ( Q .\/ R ) ) )

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
    wne
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cQ
    cR
    wne
    cP
    cQ
    cR
    c.or
    co
    c.le
    wbr
    #
    wn
    @10
    cR
    cQ
    @10
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @13
    wcel
    #
    cQ
    @13
    wcel
    #
    @8
    cR
    cQ
    wne
    @0
    @4
    @12
    @9
    cK
    hllat
    3ad2ant1
    @10
    @3
    @14
    @0
    @1
    @2
    @3
    @9
    simp23
    #
    cA
    @13
    cR
    cK
    @13
    eqid
    #
    3noncol.a
    atbase
    syl
    @10
    @1
    @15
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    cA
    @13
    cP
    cK
    @18
    3noncol.a
    atbase
    syl
    @10
    @2
    @16
    @0
    @1
    @2
    @3
    @9
    simp22
    #
    cA
    @13
    cQ
    cK
    @18
    3noncol.a
    atbase
    syl
    @0
    @4
    @5
    @8
    simp3r
    #
    @13
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @18
    3noncol.l
    3noncol.j
    latnlej1r
    syl131anc
    necomd
    @10
    @11
    @7
    @21
    @10
    @11
    cR
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @7
    @10
    @0
    @1
    @3
    @2
    @5
    @11
    @23
    wi
    @0
    @4
    @9
    simp1
    #
    @19
    @17
    @20
    @0
    @4
    @5
    @8
    simp3l
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    3noncol.l
    3noncol.j
    3noncol.a
    hlatexch1
    syl131anc
    @10
    @6
    @22
    cR
    c.le
    @10
    @0
    @1
    @2
    @6
    @22
    wceq
    @24
    @19
    @20
    cA
    c.or
    cK
    cP
    cQ
    3noncol.j
    3noncol.a
    hlatjcom
    syl3anc
    breq2d
    sylibrd
    mtod
    jca
end
