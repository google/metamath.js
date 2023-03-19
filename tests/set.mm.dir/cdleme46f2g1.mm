include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "3jca.mm"
include "simp21.mm"
include "necomd.mm"
include "simp22.mm"
include "simp23.mm"
include "wceq.mm"
include "simpl1l.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "biimp3a.mm"

theorem cdleme46f2g1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdleme46fg.j: |- .\/ = ( join ` K )
  assume cdleme46fg.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( Q =/= P /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( Q .\/ P ) /\ -. S .<_ ( Q .\/ P ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
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
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
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
    cS
    @14
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    @2
    @8
    @5
    w3a
    cQ
    cP
    wne
    #
    @11
    @12
    w3a
    cR
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @21
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @19
    @2
    @8
    @5
    @2
    @5
    @8
    @13
    @18
    simp11
    @2
    @5
    @8
    @13
    @18
    simp13
    @2
    @5
    @8
    @13
    @18
    simp12
    3jca
    @19
    @20
    @11
    @12
    @19
    cP
    cQ
    @9
    @10
    @11
    @12
    @18
    simp21
    necomd
    @9
    @10
    @11
    @12
    @18
    simp22
    @9
    @10
    @11
    @12
    @18
    simp23
    3jca
    @9
    @13
    @18
    @25
    @9
    @13
    wa
    #
    @15
    @22
    @17
    @24
    @26
    @14
    @21
    cR
    c.le
    @26
    @0
    @3
    @6
    @14
    @21
    wceq
    @0
    @1
    @5
    @8
    @13
    simpl1l
    @3
    @4
    @2
    @8
    @13
    simpl2l
    @6
    @7
    @2
    @5
    @13
    simpl3l
    cA
    c.or
    cK
    cP
    cQ
    cdleme46fg.j
    cdleme46fg.a
    hlatjcom
    syl3anc
    #
    breq2d
    @26
    @16
    @23
    @26
    @14
    @21
    cS
    c.le
    @27
    breq2d
    notbid
    anbi12d
    biimp3a
    3jca
end
