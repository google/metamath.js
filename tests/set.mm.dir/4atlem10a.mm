include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp11.mm"
include "simp21.mm"
include "simp22.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "simp23.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp3.mm"
include "hlexchb2.mm"
include "syl131anc.mm"
include "4atlem4c.mm"
include "syl12anc.mm"
include "breq2d.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"

theorem 4atlem10a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ V e. A /\ W e. A ) /\ -. R .<_ ( ( P .\/ Q ) .\/ W ) ) -> ( R .<_ ( ( P .\/ Q ) .\/ ( V .\/ W ) ) <-> ( ( P .\/ Q ) .\/ ( R .\/ W ) ) = ( ( P .\/ Q ) .\/ ( V .\/ W ) ) ) )

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
    cV
    cA
    wcel
    #
    cW
    cA
    wcel
    #
    w3a
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
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    cR
    cV
    @9
    c.or
    co
    #
    c.le
    wbr
    #
    cR
    @9
    c.or
    co
    #
    @12
    wceq
    #
    cR
    @8
    cV
    cW
    c.or
    co
    c.or
    co
    #
    c.le
    wbr
    @8
    cR
    cW
    c.or
    co
    c.or
    co
    #
    @16
    wceq
    @11
    @0
    @4
    @5
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    @13
    @15
    wb
    @0
    @1
    @2
    @7
    @10
    simp11
    #
    @3
    @4
    @5
    @6
    @10
    simp21
    #
    @3
    @4
    @5
    @6
    @10
    simp22
    #
    @11
    cK
    clat
    wcel
    #
    @8
    @18
    wcel
    #
    cW
    @18
    wcel
    #
    @19
    @11
    @0
    @23
    @20
    cK
    hllat
    syl
    @11
    @3
    @24
    @3
    @7
    @10
    simp1
    #
    cA
    @18
    c.or
    cK
    cP
    cQ
    @18
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl
    @11
    @6
    @25
    @3
    @4
    @5
    @6
    @10
    simp23
    #
    cA
    @18
    cW
    cK
    @27
    4at.a
    atbase
    syl
    @18
    c.or
    cK
    @8
    cW
    @27
    4at.j
    latjcl
    syl3anc
    @3
    @7
    @10
    simp3
    cA
    @18
    cR
    cV
    c.or
    cK
    c.le
    @9
    @27
    4at.l
    4at.j
    4at.a
    hlexchb2
    syl131anc
    @11
    @16
    @12
    cR
    c.le
    @11
    @3
    @5
    @6
    @16
    @12
    wceq
    @26
    @22
    @28
    cA
    cP
    cQ
    cV
    cW
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    4atlem4c
    syl12anc
    #
    breq2d
    @11
    @17
    @14
    @16
    @12
    @11
    @3
    @4
    @6
    @17
    @14
    wceq
    @26
    @21
    @28
    cA
    cP
    cQ
    cR
    cW
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    4atlem4c
    syl12anc
    @29
    eqeq12d
    3bitr4d
end
