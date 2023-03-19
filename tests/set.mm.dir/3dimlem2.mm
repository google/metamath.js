include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "simp3l.mm"
include "simp22.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "3ad2ant1.mm"
include "simp3r.mm"
include "wb.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "simp13.mm"
include "hlatexchb1.mm"
include "syl131anc.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "mtbird.mm"
include "simp23.mm"
include "oveq1d.mm"
include "3jca.mm"

theorem 3dimlem2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ -. S .<_ ( Q .\/ R ) /\ -. T .<_ ( ( Q .\/ R ) .\/ S ) ) /\ ( P =/= Q /\ P .<_ ( Q .\/ R ) ) ) -> ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( ( P .\/ Q ) .\/ S ) ) )

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
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cT
    @5
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cP
    @5
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @12
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    cT
    @16
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @3
    @11
    @12
    @13
    simp3l
    #
    @15
    @17
    @6
    @3
    @4
    @7
    @10
    @14
    simp22
    @15
    @16
    @5
    cS
    c.le
    @15
    @16
    cQ
    cP
    c.or
    co
    #
    @5
    @3
    @11
    @16
    @21
    wceq
    @14
    cA
    c.or
    cK
    cP
    cQ
    3dim0.j
    3dim0.a
    hlatjcom
    3ad2ant1
    @15
    @13
    @21
    @5
    wceq
    #
    @3
    @11
    @12
    @13
    simp3r
    @15
    @0
    @1
    @4
    @2
    @12
    @13
    @22
    wb
    @0
    @1
    @2
    @11
    @14
    simp11
    @0
    @1
    @2
    @11
    @14
    simp12
    @3
    @4
    @7
    @10
    @14
    simp21
    @0
    @1
    @2
    @11
    @14
    simp13
    @20
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    3dim0.l
    3dim0.j
    3dim0.a
    hlatexchb1
    syl131anc
    mpbid
    eqtrd
    #
    breq2d
    mtbird
    @15
    @19
    @9
    @3
    @4
    @7
    @10
    @14
    simp23
    @15
    @18
    @8
    cT
    c.le
    @15
    @16
    @5
    cS
    c.or
    @23
    oveq1d
    breq2d
    mtbird
    3jca
end
