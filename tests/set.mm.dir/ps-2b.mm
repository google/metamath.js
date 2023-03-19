include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "3jca.mm"
include "simp22.mm"
include "simp23.mm"
include "jca.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "ps-2.mm"
include "syl32anc.mm"
include "cal.mm"
include "cbs.mm"
include "cfv.mm"
include "simp111.mm"
include "hlatl.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simp112.mm"
include "simp121.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp122.mm"
include "simp123.mm"
include "latmcl.mm"
include "simp2.mm"
include "simp3.mm"
include "wb.mm"
include "atbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "atlen0.mm"
include "syl31anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem ps-2b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.0: class .0.
  let vu: setvar u
  assume ps-2b.l: |- .<_ = ( le ` K )
  assume ps-2b.j: |- .\/ = ( join ` K )
  assume ps-2b.m: |- ./\ = ( meet ` K )
  assume ps-2b.z: |- .0. = ( 0. ` K )
  assume ps-2b.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( -. P .<_ ( Q .\/ R ) /\ S =/= T /\ ( S .<_ ( P .\/ Q ) /\ T .<_ ( Q .\/ R ) ) ) ) -> ( ( P .\/ R ) ./\ ( S .\/ T ) ) =/= .0. )

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
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    cT
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    cT
    @8
    c.le
    wbr
    wa
    #
    w3a
    #
    w3a
    #
    vu
    cv
    #
    cP
    cR
    c.or
    co
    #
    c.le
    wbr
    @14
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    wa
    #
    vu
    cA
    wrex
    #
    @15
    @16
    c.an
    co
    #
    c.0
    wne
    #
    @13
    @0
    @1
    @2
    @4
    w3a
    @5
    @6
    wa
    @9
    @10
    wa
    @11
    @18
    @0
    @1
    @2
    @7
    @12
    simp11
    @13
    @1
    @2
    @4
    @0
    @1
    @2
    @7
    @12
    simp12
    @0
    @1
    @2
    @7
    @12
    simp13
    @3
    @4
    @5
    @6
    @12
    simp21
    3jca
    @13
    @5
    @6
    @3
    @4
    @5
    @6
    @12
    simp22
    @3
    @4
    @5
    @6
    @12
    simp23
    jca
    @13
    @9
    @10
    @3
    @7
    @9
    @10
    @11
    simp31
    @3
    @7
    @9
    @10
    @11
    simp32
    jca
    @3
    @7
    @9
    @10
    @11
    simp33
    vu
    cA
    cP
    cQ
    cR
    cS
    cT
    c.or
    cK
    c.le
    ps-2b.l
    ps-2b.j
    ps-2b.a
    ps-2
    syl32anc
    @13
    @17
    @20
    vu
    cA
    @13
    @14
    cA
    wcel
    #
    @17
    w3a
    #
    cK
    cal
    wcel
    #
    @19
    cK
    cbs
    cfv
    #
    wcel
    #
    @21
    @14
    @19
    c.le
    wbr
    #
    @20
    @22
    @0
    @23
    @0
    @1
    @2
    @7
    @12
    @21
    @17
    simp111
    #
    cK
    hlatl
    syl
    @22
    cK
    clat
    wcel
    #
    @15
    @24
    wcel
    #
    @16
    @24
    wcel
    #
    @25
    @22
    @0
    @28
    @27
    cK
    hllat
    syl
    #
    @22
    @0
    @1
    @4
    @29
    @27
    @0
    @1
    @2
    @7
    @12
    @21
    @17
    simp112
    @4
    @5
    @6
    @3
    @12
    @21
    @17
    simp121
    cA
    @24
    c.or
    cK
    cP
    cR
    @24
    eqid
    #
    ps-2b.j
    ps-2b.a
    hlatjcl
    syl3anc
    #
    @22
    @0
    @5
    @6
    @30
    @27
    @4
    @5
    @6
    @3
    @12
    @21
    @17
    simp122
    @4
    @5
    @6
    @3
    @12
    @21
    @17
    simp123
    cA
    @24
    c.or
    cK
    cS
    cT
    @32
    ps-2b.j
    ps-2b.a
    hlatjcl
    syl3anc
    #
    @24
    cK
    c.an
    @15
    @16
    @32
    ps-2b.m
    latmcl
    syl3anc
    @13
    @21
    @17
    simp2
    #
    @22
    @17
    @26
    @13
    @21
    @17
    simp3
    @22
    @28
    @14
    @24
    wcel
    #
    @29
    @30
    @17
    @26
    wb
    @31
    @22
    @21
    @36
    @35
    cA
    @24
    @14
    cK
    @32
    ps-2b.a
    atbase
    syl
    @33
    @34
    @24
    cK
    c.le
    c.an
    @14
    @15
    @16
    @32
    ps-2b.l
    ps-2b.m
    latlem12
    syl13anc
    mpbid
    cA
    @24
    @14
    cK
    c.le
    @19
    c.0
    @32
    ps-2b.l
    ps-2b.z
    ps-2b.a
    atlen0
    syl31anc
    rexlimdv3a
    mpd
end
