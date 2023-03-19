include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simpr1.mm"
include "simpr2.mm"
include "wi.mm"
include "simpl11.mm"
include "simpl2l.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl3l.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "mtod.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3r.mm"
include "simpr3.mm"
include "3dimlem3a.mm"
include "syl113anc.mm"
include "3jca.mm"

theorem 3dimlem3
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


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( Q =/= R /\ -. T .<_ ( ( Q .\/ R ) .\/ S ) ) ) /\ ( P =/= Q /\ -. P .<_ ( Q .\/ R ) /\ P .<_ ( ( Q .\/ R ) .\/ S ) ) ) -> ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. T .<_ ( ( P .\/ Q ) .\/ R ) ) )

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
    cT
    cQ
    cR
    c.or
    co
    #
    cS
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
    cP
    @9
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @13
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
    cT
    @19
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    @12
    @13
    @15
    @16
    simpr1
    @18
    @20
    @14
    @12
    @13
    @15
    @16
    simpr2
    #
    @18
    @20
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @14
    @18
    @0
    @4
    @1
    @2
    cR
    cQ
    wne
    @20
    @24
    wi
    @0
    @1
    @2
    @6
    @11
    @17
    simpl11
    #
    @4
    @5
    @3
    @11
    @17
    simpl2l
    #
    @0
    @1
    @2
    @6
    @11
    @17
    simpl12
    @0
    @1
    @2
    @6
    @11
    @17
    simpl13
    #
    @18
    cQ
    cR
    @7
    @10
    @3
    @6
    @17
    simpl3l
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
    @18
    @8
    @23
    cP
    c.le
    @18
    @0
    @2
    @4
    @8
    @23
    wceq
    @25
    @27
    @26
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
    mtod
    @18
    @3
    @6
    @10
    @15
    @16
    @21
    @3
    @6
    @11
    @17
    simpl1
    @3
    @6
    @11
    @17
    simpl2
    @7
    @10
    @3
    @6
    @17
    simpl3r
    @22
    @12
    @13
    @15
    @16
    simpr3
    cA
    cP
    cQ
    cR
    cS
    cT
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem3a
    syl113anc
    3jca
end
