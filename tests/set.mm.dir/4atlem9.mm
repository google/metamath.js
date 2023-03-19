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
include "simp22.mm"
include "simp23.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "simp21.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp3.mm"
include "hlexchb2.mm"
include "syl131anc.mm"
include "4atlem4d.mm"
include "syl12anc.mm"
include "breq2d.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"

theorem 4atlem9
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ W e. A ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) -> ( S .<_ ( ( P .\/ Q ) .\/ ( R .\/ W ) ) <-> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( P .\/ Q ) .\/ ( R .\/ W ) ) ) )

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
    cW
    cA
    wcel
    #
    w3a
    #
    cS
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    cS
    cW
    @9
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @9
    c.or
    co
    #
    @12
    wceq
    #
    cS
    @8
    cR
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
    cS
    c.or
    co
    c.or
    co
    #
    @16
    wceq
    @11
    @0
    @5
    @6
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
    simp22
    #
    @3
    @4
    @5
    @6
    @10
    simp23
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
    cR
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
    @4
    @25
    @3
    @4
    @5
    @6
    @10
    simp21
    #
    cA
    @18
    cR
    cK
    @27
    4at.a
    atbase
    syl
    @18
    c.or
    cK
    @8
    cR
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
    cS
    cW
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
    cS
    c.le
    @11
    @3
    @4
    @6
    @16
    @12
    wceq
    @26
    @28
    @22
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
    4atlem4d
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
    @5
    @17
    @14
    wceq
    @26
    @28
    @21
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    4atlem4d
    syl12anc
    @29
    eqeq12d
    3bitr4d
end
