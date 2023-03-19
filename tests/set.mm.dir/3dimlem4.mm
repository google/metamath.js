include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp2l.mm"
include "simp2r.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3l.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "3ad2ant1.mm"
include "mtod.mm"
include "simp13r.mm"
include "simp3.mm"
include "3dimlem4a.mm"
include "syl113anc.mm"
include "3jca.mm"

theorem 3dimlem4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
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


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( Q =/= R /\ -. S .<_ ( Q .\/ R ) ) ) /\ ( P =/= Q /\ -. P .<_ ( Q .\/ R ) ) /\ -. P .<_ ( ( Q .\/ R ) .\/ S ) ) -> ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) )

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
    cA
    wcel
    #
    wa
    #
    cQ
    cR
    wne
    #
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cP
    @8
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cP
    @8
    cS
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    @12
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
    cS
    @18
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    @11
    @12
    @14
    @16
    simp2l
    @17
    @19
    @13
    @11
    @12
    @14
    @16
    simp2r
    #
    @11
    @15
    @19
    @13
    wi
    @16
    @11
    @19
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @13
    @11
    @0
    @4
    @1
    @2
    cR
    cQ
    wne
    @19
    @23
    wi
    @0
    @1
    @2
    @6
    @10
    simp11
    #
    @3
    @4
    @5
    @10
    simp2l
    #
    @0
    @1
    @2
    @6
    @10
    simp12
    @0
    @1
    @2
    @6
    @10
    simp13
    #
    @11
    cQ
    cR
    @3
    @6
    @7
    @9
    simp3l
    necomd
    cA
    cR
    cP
    cQ
    c.or
    cK
    c.le
    3dim0.l
    3dim0.j
    3dim0.a
    hlatexch2
    syl131anc
    @11
    @8
    @22
    cP
    c.le
    @11
    @0
    @2
    @4
    @8
    @22
    wceq
    @24
    @26
    @25
    cA
    c.or
    cK
    cQ
    cR
    3dim0.j
    3dim0.a
    hlatjcom
    syl3anc
    breq2d
    sylibrd
    3ad2ant1
    mtod
    @17
    @3
    @6
    @9
    @14
    @16
    @20
    @3
    @6
    @10
    @15
    @16
    simp11
    @3
    @6
    @10
    @15
    @16
    simp12
    @7
    @9
    @3
    @6
    @15
    @16
    simp13r
    @21
    @11
    @15
    @16
    simp3
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem4a
    syl113anc
    3jca
end
