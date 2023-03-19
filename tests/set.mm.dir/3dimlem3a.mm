include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp31.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp13.mm"
include "eqid.mm"
include "atbase.mm"
include "simp2l.mm"
include "simp12.mm"
include "latjrot.mm"
include "syl13anc.mm"
include "simp33.mm"
include "wb.mm"
include "simp2r.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp32.mm"
include "hlexchb1.mm"
include "syl131anc.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "mtbird.mm"

theorem 3dimlem3a
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


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( -. T .<_ ( ( Q .\/ R ) .\/ S ) /\ -. P .<_ ( Q .\/ R ) /\ P .<_ ( ( Q .\/ R ) .\/ S ) ) ) -> -. T .<_ ( ( P .\/ Q ) .\/ R ) )

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
    #
    wn
    #
    cP
    @7
    c.le
    wbr
    wn
    #
    cP
    @8
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cT
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    #
    c.le
    wbr
    @9
    @3
    @6
    @10
    @11
    @12
    simp31
    @14
    @15
    @8
    cT
    c.le
    @14
    @7
    cP
    c.or
    co
    #
    @15
    @8
    @14
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @18
    wcel
    #
    cP
    @18
    wcel
    #
    @16
    @15
    wceq
    @14
    @0
    @17
    @0
    @1
    @2
    @6
    @13
    simp11
    #
    cK
    hllat
    syl
    @14
    @2
    @19
    @0
    @1
    @2
    @6
    @13
    simp13
    #
    cA
    @18
    cQ
    cK
    @18
    eqid
    #
    3dim0.a
    atbase
    syl
    @14
    @4
    @20
    @3
    @4
    @5
    @13
    simp2l
    #
    cA
    @18
    cR
    cK
    @24
    3dim0.a
    atbase
    syl
    @14
    @1
    @21
    @0
    @1
    @2
    @6
    @13
    simp12
    #
    cA
    @18
    cP
    cK
    @24
    3dim0.a
    atbase
    syl
    @18
    c.or
    cK
    cQ
    cR
    cP
    @24
    3dim0.j
    latjrot
    syl13anc
    @14
    @12
    @16
    @8
    wceq
    #
    @3
    @6
    @10
    @11
    @12
    simp33
    @14
    @0
    @1
    @5
    @7
    @18
    wcel
    #
    @11
    @12
    @27
    wb
    @22
    @26
    @3
    @4
    @5
    @13
    simp2r
    @14
    @0
    @2
    @4
    @28
    @22
    @23
    @25
    cA
    @18
    c.or
    cK
    cQ
    cR
    @24
    3dim0.j
    3dim0.a
    hlatjcl
    syl3anc
    @3
    @6
    @10
    @11
    @12
    simp32
    cA
    @18
    cP
    cS
    c.or
    cK
    c.le
    @7
    @24
    3dim0.l
    3dim0.j
    3dim0.a
    hlexchb1
    syl131anc
    mpbid
    eqtr3d
    breq2d
    mtbird
end
