include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wi.mm"
include "wa.mm"
include "weq.mm"
include "breq1.mm"
include "biimpac.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "clat.mm"
include "simpll1.mm"
include "hllat.mm"
include "syl.mm"
include "simpll2.mm"
include "atbase.mm"
include "simp32.mm"
include "ad2antrr.mm"
include "simp33.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp31.mm"
include "simplr.mm"
include "hlatlej2.mm"
include "simpr.mm"
include "latjle12.mm"
include "biimpd.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "lattrd.mm"
include "ex.mm"
include "syl5.mm"
include "expdimp.mm"
include "necon3bd.mm"
include "exp31.mm"
include "com23.mm"
include "com24.mm"
include "3imp2.mm"

theorem paddasslem5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ r e. A /\ ( x e. A /\ y e. A /\ z e. A ) ) /\ ( -. r .<_ ( x .\/ y ) /\ r .<_ ( y .\/ z ) /\ s .<_ ( x .\/ y ) ) ) -> s =/= z )

  proof
    cK
    chlt
    wcel
    #
    vr
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    w3a
    #
    w3a
    #
    @1
    @3
    @5
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @1
    @5
    @7
    c.or
    co
    #
    c.le
    wbr
    #
    vs
    cv
    #
    @11
    c.le
    wbr
    #
    @16
    @7
    wne
    #
    @10
    @17
    @15
    @13
    @18
    @10
    @15
    @17
    @13
    @18
    wi
    #
    @10
    @15
    @17
    @19
    @10
    @15
    wa
    #
    @17
    wa
    @12
    @16
    @7
    @20
    @17
    vs
    vz
    weq
    #
    @12
    @17
    @21
    wa
    @7
    @11
    c.le
    wbr
    #
    @20
    @12
    @21
    @17
    @22
    @16
    @7
    @11
    c.le
    breq1
    biimpac
    @20
    @22
    @12
    @20
    @22
    wa
    #
    cK
    cbs
    cfv
    #
    cK
    c.le
    @1
    @14
    @11
    @24
    eqid
    #
    paddasslem.l
    @23
    @0
    cK
    clat
    wcel
    #
    @0
    @2
    @9
    @15
    @22
    simpll1
    #
    cK
    hllat
    syl
    #
    @23
    @2
    @1
    @24
    wcel
    @0
    @2
    @9
    @15
    @22
    simpll2
    cA
    @24
    @1
    cK
    @25
    paddasslem.a
    atbase
    syl
    @23
    @26
    @5
    @24
    wcel
    #
    @7
    @24
    wcel
    #
    @14
    @24
    wcel
    @28
    @23
    @6
    @29
    @10
    @6
    @15
    @22
    @0
    @2
    @4
    @6
    @8
    simp32
    ad2antrr
    #
    cA
    @24
    @5
    cK
    @25
    paddasslem.a
    atbase
    syl
    #
    @23
    @8
    @30
    @10
    @8
    @15
    @22
    @0
    @2
    @4
    @6
    @8
    simp33
    ad2antrr
    cA
    @24
    @7
    cK
    @25
    paddasslem.a
    atbase
    syl
    #
    @24
    c.or
    cK
    @5
    @7
    @25
    paddasslem.j
    latjcl
    syl3anc
    @23
    @26
    @3
    @24
    wcel
    #
    @29
    @11
    @24
    wcel
    #
    @28
    @23
    @4
    @34
    @10
    @4
    @15
    @22
    @0
    @2
    @4
    @6
    @8
    simp31
    ad2antrr
    #
    cA
    @24
    @3
    cK
    @25
    paddasslem.a
    atbase
    syl
    @32
    @24
    c.or
    cK
    @3
    @5
    @25
    paddasslem.j
    latjcl
    syl3anc
    #
    @10
    @15
    @22
    simplr
    @23
    @5
    @11
    c.le
    wbr
    #
    @22
    @14
    @11
    c.le
    wbr
    #
    @23
    @0
    @4
    @6
    @38
    @27
    @36
    @31
    cA
    @3
    @5
    c.or
    cK
    c.le
    paddasslem.l
    paddasslem.j
    paddasslem.a
    hlatlej2
    syl3anc
    @20
    @22
    simpr
    @23
    @26
    @29
    @30
    @35
    @38
    @22
    wa
    #
    @39
    wi
    @28
    @32
    @33
    @37
    @26
    @29
    @30
    @35
    w3a
    wa
    @40
    @39
    @24
    c.or
    cK
    c.le
    @5
    @7
    @11
    @25
    paddasslem.l
    paddasslem.j
    latjle12
    biimpd
    syl13anc
    mp2and
    lattrd
    ex
    syl5
    expdimp
    necon3bd
    exp31
    com23
    com24
    3imp2
end
