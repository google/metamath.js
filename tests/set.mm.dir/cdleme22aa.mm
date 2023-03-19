include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp33.mm"
include "simp32.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp31.mm"
include "eqid.mm"
include "atbase.mm"
include "simp21l.mm"
include "simp22.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "syl6breqr.mm"
include "cal.mm"
include "hlatl.mm"
include "simp21r.mm"
include "simp23.mm"
include "cdleme0a.mm"
include "syl222anc.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdleme22aa
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )
  assume cdleme22.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ P =/= Q ) /\ ( V e. A /\ V .<_ W /\ V .<_ ( P .\/ Q ) ) ) -> V = U )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    cV
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cV
    cU
    c.le
    wbr
    #
    cV
    cU
    wceq
    #
    @14
    cV
    @11
    cW
    c.an
    co
    #
    cU
    c.le
    @14
    @12
    @10
    cV
    @17
    c.le
    wbr
    #
    @2
    @8
    @9
    @10
    @12
    simp33
    @2
    @8
    @9
    @10
    @12
    simp32
    @14
    cK
    clat
    wcel
    #
    cV
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    @20
    wcel
    #
    cW
    @20
    wcel
    #
    @12
    @10
    wa
    @18
    wb
    @14
    @0
    @19
    @0
    @1
    @8
    @13
    simp1l
    #
    cK
    hllat
    syl
    @14
    @9
    @21
    @2
    @8
    @9
    @10
    @12
    simp31
    #
    cA
    @20
    cV
    cK
    @20
    eqid
    #
    cdleme22.a
    atbase
    syl
    @14
    @0
    @3
    @6
    @22
    @24
    @3
    @4
    @6
    @7
    @2
    @13
    simp21l
    #
    @2
    @5
    @6
    @7
    @13
    simp22
    #
    cA
    @20
    c.or
    cK
    cP
    cQ
    @26
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    @14
    @1
    @23
    @0
    @1
    @8
    @13
    simp1r
    #
    @20
    cH
    cK
    cW
    @26
    cdleme22.h
    lhpbase
    syl
    @20
    cK
    c.le
    c.an
    cV
    @11
    cW
    @26
    cdleme22.l
    cdleme22.m
    latlem12
    syl13anc
    mpbi2and
    cdleme22.u
    syl6breqr
    @14
    cK
    cal
    wcel
    #
    @9
    cU
    cA
    wcel
    #
    @15
    @16
    wb
    @14
    @0
    @30
    @24
    cK
    hlatl
    syl
    @25
    @14
    @0
    @1
    @3
    @4
    @6
    @7
    @31
    @24
    @29
    @27
    @3
    @4
    @6
    @7
    @2
    @13
    simp21r
    @28
    @2
    @5
    @6
    @7
    @13
    simp23
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22.u
    cdleme0a
    syl222anc
    cA
    cV
    cU
    cK
    c.le
    cdleme22.l
    cdleme22.a
    atcmp
    syl3anc
    mpbid
end
