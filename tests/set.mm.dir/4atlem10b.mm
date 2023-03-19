include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "simprr.mm"
include "simprl.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl32.mm"
include "4atlem10a.mm"
include "syl131anc.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "simpl22.mm"
include "simpl33.mm"
include "4atlem9.mm"
include "eqtrd.mm"

theorem 4atlem10b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ V e. A ) /\ ( W e. A /\ -. R .<_ ( ( P .\/ Q ) .\/ W ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) /\ ( R .<_ ( ( P .\/ Q ) .\/ ( V .\/ W ) ) /\ S .<_ ( ( P .\/ Q ) .\/ ( V .\/ W ) ) ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( P .\/ Q ) .\/ ( V .\/ W ) ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    w3a
    #
    cW
    cA
    wcel
    #
    cR
    cP
    cQ
    c.or
    co
    #
    cW
    c.or
    co
    c.le
    wbr
    wn
    #
    cS
    @6
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cR
    @6
    cV
    cW
    c.or
    co
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @11
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @6
    cR
    cS
    c.or
    co
    c.or
    co
    #
    @6
    cR
    cW
    c.or
    co
    c.or
    co
    #
    @11
    @15
    cS
    @17
    c.le
    wbr
    #
    @16
    @17
    wceq
    #
    @15
    cS
    @11
    @17
    c.le
    @10
    @12
    @13
    simprr
    @15
    @12
    @17
    @11
    wceq
    #
    @10
    @12
    @13
    simprl
    @15
    @0
    @1
    @3
    @5
    @7
    @12
    @20
    wb
    @0
    @4
    @9
    @14
    simpl1
    #
    @1
    @2
    @3
    @0
    @9
    @14
    simpl21
    #
    @1
    @2
    @3
    @0
    @9
    @14
    simpl23
    @5
    @7
    @8
    @0
    @4
    @14
    simpl31
    #
    @5
    @7
    @8
    @0
    @4
    @14
    simpl32
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem10a
    syl131anc
    mpbid
    #
    breqtrrd
    @15
    @0
    @1
    @2
    @5
    @8
    @18
    @19
    wb
    @21
    @22
    @1
    @2
    @3
    @0
    @9
    @14
    simpl22
    @23
    @5
    @7
    @8
    @0
    @4
    @14
    simpl33
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    cW
    4at.l
    4at.j
    4at.a
    4atlem9
    syl131anc
    mpbid
    @24
    eqtrd
end
