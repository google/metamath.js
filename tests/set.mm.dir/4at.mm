include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "4atlem12.mm"
include "wi.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp23.mm"
include "simp31.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp32.mm"
include "simp33.mm"
include "latjcl.mm"
include "latref.mm"
include "syl2anc.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "impbid.mm"

theorem 4at
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( U e. A /\ V e. A /\ W e. A ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( ( ( P .\/ Q ) .\/ ( R .\/ S ) ) .<_ ( ( T .\/ U ) .\/ ( V .\/ W ) ) <-> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( T .\/ U ) .\/ ( V .\/ W ) ) ) )

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
    cT
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
    w3a
    #
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cS
    @13
    cR
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    wa
    @13
    cR
    cS
    c.or
    co
    c.or
    co
    #
    cT
    cU
    c.or
    co
    #
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
    #
    @15
    @18
    wceq
    #
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem12
    @12
    @20
    @19
    wi
    @14
    @12
    @19
    @20
    @18
    @18
    c.le
    wbr
    #
    @12
    cK
    clat
    wcel
    #
    @18
    cK
    cbs
    cfv
    #
    wcel
    #
    @21
    @12
    @0
    @22
    @0
    @1
    @2
    @7
    @11
    simp11
    #
    cK
    hllat
    syl
    #
    @12
    @22
    @16
    @23
    wcel
    #
    @17
    @23
    wcel
    #
    @24
    @26
    @12
    @0
    @6
    @8
    @27
    @25
    @3
    @4
    @5
    @6
    @11
    simp23
    @3
    @7
    @8
    @9
    @10
    simp31
    cA
    @23
    c.or
    cK
    cT
    cU
    @23
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @12
    @0
    @9
    @10
    @28
    @25
    @3
    @7
    @8
    @9
    @10
    simp32
    @3
    @7
    @8
    @9
    @10
    simp33
    cA
    @23
    c.or
    cK
    cV
    cW
    @29
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @23
    c.or
    cK
    @16
    @17
    @29
    4at.j
    latjcl
    syl3anc
    @23
    cK
    c.le
    @18
    @29
    4at.l
    latref
    syl2anc
    @15
    @18
    @18
    c.le
    breq1
    syl5ibrcom
    adantr
    impbid
end
