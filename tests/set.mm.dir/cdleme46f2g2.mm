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
include "simp2l.mm"
include "necomd.mm"
include "simp2r.mm"
include "jca.mm"
include "wceq.mm"
include "simpl1l.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "notbid.mm"
include "biimp3a.mm"

theorem cdleme46f2g2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdleme46fg.j: |- .\/ = ( join ` K )
  assume cdleme46fg.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( Q =/= P /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( Q .\/ P ) ) )

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
    wa
    #
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
    wa
    cS
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @16
    @2
    @8
    @5
    @2
    @5
    @8
    @12
    @15
    simp11
    @2
    @5
    @8
    @12
    @15
    simp13
    @2
    @5
    @8
    @12
    @15
    simp12
    3jca
    @16
    @17
    @11
    @16
    cP
    cQ
    @9
    @10
    @11
    @15
    simp2l
    necomd
    @9
    @10
    @11
    @15
    simp2r
    jca
    @9
    @12
    @15
    @20
    @9
    @12
    wa
    #
    @14
    @19
    @21
    @13
    @18
    cS
    c.le
    @21
    @0
    @3
    @6
    @13
    @18
    wceq
    @0
    @1
    @5
    @8
    @12
    simpl1l
    @3
    @4
    @2
    @8
    @12
    simpl2l
    @6
    @7
    @2
    @5
    @12
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
    breq2d
    notbid
    biimp3a
    3jca
end
