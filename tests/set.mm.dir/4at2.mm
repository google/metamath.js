include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "4at.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "atbase.mm"
include "simp22.mm"
include "latjass.mm"
include "syl13anc.mm"
include "simp23.mm"
include "simp31.mm"
include "syl3anc.mm"
include "simp32.mm"
include "simp33.mm"
include "breq12d.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"

theorem 4at2
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


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( U e. A /\ V e. A /\ W e. A ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( ( ( ( P .\/ Q ) .\/ R ) .\/ S ) .<_ ( ( ( T .\/ U ) .\/ V ) .\/ W ) <-> ( ( ( P .\/ Q ) .\/ R ) .\/ S ) = ( ( ( T .\/ U ) .\/ V ) .\/ W ) ) )

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
    #
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
    c.or
    co
    #
    c.le
    wbr
    #
    @16
    @18
    wceq
    #
    @14
    cS
    c.or
    co
    #
    @17
    cV
    c.or
    co
    cW
    c.or
    co
    #
    c.le
    wbr
    #
    @21
    @22
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
    4at
    @12
    @23
    @19
    wb
    @15
    @12
    @21
    @16
    @22
    @18
    c.le
    @12
    cK
    clat
    wcel
    #
    @13
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @26
    wcel
    #
    cS
    @26
    wcel
    #
    @21
    @16
    wceq
    @12
    @0
    @25
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
    @3
    @7
    @27
    @11
    cA
    @26
    c.or
    cK
    cP
    cQ
    @26
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    3ad2ant1
    @12
    @4
    @28
    @3
    @4
    @5
    @6
    @11
    simp21
    cA
    @26
    cR
    cK
    @32
    4at.a
    atbase
    syl
    @12
    @5
    @29
    @3
    @4
    @5
    @6
    @11
    simp22
    cA
    @26
    cS
    cK
    @32
    4at.a
    atbase
    syl
    @26
    c.or
    cK
    @13
    cR
    cS
    @32
    4at.j
    latjass
    syl13anc
    #
    @12
    @25
    @17
    @26
    wcel
    #
    cV
    @26
    wcel
    #
    cW
    @26
    wcel
    #
    @22
    @18
    wceq
    @31
    @12
    @0
    @6
    @8
    @34
    @30
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
    @26
    c.or
    cK
    cT
    cU
    @32
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @12
    @9
    @35
    @3
    @7
    @8
    @9
    @10
    simp32
    cA
    @26
    cV
    cK
    @32
    4at.a
    atbase
    syl
    @12
    @10
    @36
    @3
    @7
    @8
    @9
    @10
    simp33
    cA
    @26
    cW
    cK
    @32
    4at.a
    atbase
    syl
    @26
    c.or
    cK
    @17
    cV
    cW
    @32
    4at.j
    latjass
    syl13anc
    #
    breq12d
    adantr
    @12
    @24
    @20
    wb
    @15
    @12
    @21
    @16
    @22
    @18
    @33
    @37
    eqeq12d
    adantr
    3bitr4d
end
