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
include "simp13.mm"
include "simp21.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp23.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp3.mm"
include "hlexchb2.mm"
include "syl131anc.mm"
include "4atlem4b.mm"
include "syl32anc.mm"
include "breq2d.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"

theorem 4atlem11a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( U e. A /\ V e. A /\ W e. A ) /\ -. Q .<_ ( ( P .\/ V ) .\/ W ) ) -> ( Q .<_ ( ( P .\/ U ) .\/ ( V .\/ W ) ) <-> ( ( P .\/ Q ) .\/ ( V .\/ W ) ) = ( ( P .\/ U ) .\/ ( V .\/ W ) ) ) )

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
    cU
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
    cQ
    cP
    cV
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
    cQ
    cU
    @9
    c.or
    co
    #
    c.le
    wbr
    #
    cQ
    @9
    c.or
    co
    #
    @12
    wceq
    #
    cQ
    cP
    cU
    c.or
    co
    cV
    cW
    c.or
    co
    #
    c.or
    co
    #
    c.le
    wbr
    cP
    cQ
    c.or
    co
    @16
    c.or
    co
    #
    @17
    wceq
    @11
    @0
    @2
    @4
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
    @0
    @1
    @2
    @7
    @10
    simp13
    #
    @3
    @4
    @5
    @6
    @10
    simp21
    #
    @11
    cK
    clat
    wcel
    #
    @8
    @19
    wcel
    #
    cW
    @19
    wcel
    #
    @20
    @11
    @0
    @24
    @21
    cK
    hllat
    syl
    @11
    @0
    @1
    @5
    @25
    @21
    @0
    @1
    @2
    @7
    @10
    simp12
    #
    @3
    @4
    @5
    @6
    @10
    simp22
    #
    cA
    @19
    c.or
    cK
    cP
    cV
    @19
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @11
    @6
    @26
    @3
    @4
    @5
    @6
    @10
    simp23
    #
    cA
    @19
    cW
    cK
    @29
    4at.a
    atbase
    syl
    @19
    c.or
    cK
    @8
    cW
    @29
    4at.j
    latjcl
    syl3anc
    @3
    @7
    @10
    simp3
    cA
    @19
    cQ
    cU
    c.or
    cK
    c.le
    @9
    @29
    4at.l
    4at.j
    4at.a
    hlexchb2
    syl131anc
    @11
    @17
    @12
    cQ
    c.le
    @11
    @0
    @1
    @4
    @5
    @6
    @17
    @12
    wceq
    @21
    @27
    @23
    @28
    @30
    cA
    cP
    cU
    cV
    cW
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    4atlem4b
    syl32anc
    #
    breq2d
    @11
    @18
    @14
    @17
    @12
    @11
    @0
    @1
    @2
    @5
    @6
    @18
    @14
    wceq
    @21
    @27
    @22
    @28
    @30
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
    4atlem4b
    syl32anc
    @31
    eqeq12d
    3bitr4d
end
