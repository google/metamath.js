include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp123.mm"
include "3jca.mm"
include "simp2l.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp121.mm"
include "simp122.mm"
include "latnlej1l.mm"
include "syl131anc.mm"
include "necomd.mm"
include "wi.mm"
include "simp2r.mm"
include "hlatexch1.mm"
include "mtod.mm"
include "simp3.mm"
include "3atlem3.mm"
include "syl331anc.mm"

theorem 3atlem4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3at.l: |- .<_ = ( le ` K )
  assume 3at.j: |- .\/ = ( join ` K )
  assume 3at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ P =/= Q ) /\ ( ( P .\/ Q ) .\/ R ) .<_ ( ( S .\/ T ) .\/ R ) ) -> ( ( P .\/ Q ) .\/ R ) = ( ( S .\/ T ) .\/ R ) )

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
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    wa
    #
    w3a
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
    cP
    cQ
    wne
    #
    wa
    #
    @9
    cR
    c.or
    co
    #
    cS
    cT
    c.or
    co
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    @0
    @4
    @5
    @6
    @3
    w3a
    @11
    cP
    cR
    wne
    cQ
    cP
    cR
    c.or
    co
    c.le
    wbr
    #
    wn
    @16
    @14
    @15
    wceq
    @0
    @4
    @7
    @13
    @16
    simp11
    #
    @0
    @4
    @7
    @13
    @16
    simp12
    @17
    @5
    @6
    @3
    @5
    @6
    @0
    @4
    @13
    @16
    simp13l
    @5
    @6
    @0
    @4
    @13
    @16
    simp13r
    @1
    @2
    @3
    @0
    @7
    @13
    @16
    simp123
    #
    3jca
    @8
    @11
    @12
    @16
    simp2l
    #
    @17
    cR
    cP
    @17
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
    @23
    wcel
    #
    cQ
    @23
    wcel
    #
    @11
    cR
    cP
    wne
    @17
    @0
    @22
    @19
    cK
    hllat
    syl
    @17
    @3
    @24
    @20
    cA
    @23
    cR
    cK
    @23
    eqid
    #
    3at.a
    atbase
    syl
    @17
    @1
    @25
    @1
    @2
    @3
    @0
    @7
    @13
    @16
    simp121
    #
    cA
    @23
    cP
    cK
    @27
    3at.a
    atbase
    syl
    @17
    @2
    @26
    @1
    @2
    @3
    @0
    @7
    @13
    @16
    simp122
    #
    cA
    @23
    cQ
    cK
    @27
    3at.a
    atbase
    syl
    @21
    @23
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @27
    3at.l
    3at.j
    latnlej1l
    syl131anc
    necomd
    @17
    @18
    @10
    @21
    @17
    @0
    @2
    @3
    @1
    cQ
    cP
    wne
    @18
    @10
    wi
    @19
    @29
    @20
    @28
    @17
    cP
    cQ
    @8
    @11
    @12
    @16
    simp2r
    necomd
    cA
    cQ
    cR
    cP
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    hlatexch1
    syl131anc
    mtod
    @8
    @13
    @16
    simp3
    cA
    cP
    cQ
    cR
    cS
    cT
    cR
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem3
    syl331anc
end
