include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "cin.mm"
include "weq.mm"
include "wa.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "ssinss1.mm"
include "syl.mm"
include "sspadd1.mm"
include "syl3anc.mm"
include "simpr.mm"
include "simpl31.mm"
include "eqeltrd.mm"
include "sseldd.mm"
include "wne.mm"
include "clat.mm"
include "hllat.mm"
include "simpl32.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "psubssat.mm"
include "syl2anc.mm"
include "3jca.mm"
include "simpl33.mm"
include "hlatexch1.mm"
include "imp.mm"
include "syl31anc.mm"
include "csn.mm"
include "simp31.mm"
include "snssd.mm"
include "simp22.mm"
include "sstrd.mm"
include "simp23.mm"
include "wb.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "paddss.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp33.mm"
include "simp13.mm"
include "simp32.mm"
include "elpadd2at2.mm"
include "mpbird.mm"
include "syl333anc.mm"
include "elind.mm"
include "elpaddri.mm"
include "syl322anc.mm"
include "pm2.61dane.mm"

theorem pmodlem1
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume pmodlem.l: |- .<_ = ( le ` K )
  assume pmodlem.j: |- .\/ = ( join ` K )
  assume pmodlem.a: |- A = ( Atoms ` K )
  assume pmodlem.s: |- S = ( PSubSp ` K )
  assume pmodlem.p: |- .+ = ( +P ` K )

  disjoint p q
  disjoint p r
  disjoint A p
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint .\/ q
  disjoint .\/ r
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint .<_ q
  disjoint .<_ r
  disjoint .+ p
  disjoint .+ q
  disjoint .+ r
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint Z p
  disjoint Z q
  disjoint Z r
  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ ( Z e. S /\ X C_ Z /\ p e. Z ) /\ ( q e. X /\ r e. Y /\ p .<_ ( q .\/ r ) ) ) -> p e. ( X .+ ( Y i^i Z ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cZ
    cS
    wcel
    #
    cX
    cZ
    wss
    #
    vp
    cv
    #
    cZ
    wcel
    #
    w3a
    #
    vq
    cv
    #
    cX
    wcel
    #
    vr
    cv
    #
    cY
    wcel
    #
    @6
    @9
    @11
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    @6
    cX
    cY
    cZ
    cin
    #
    c.pl
    co
    #
    wcel
    #
    @6
    @9
    @15
    vp
    vq
    weq
    #
    wa
    #
    cX
    @17
    @6
    @20
    @0
    @1
    @16
    cA
    wss
    #
    cX
    @17
    wss
    @0
    @1
    @2
    @8
    @14
    @19
    simpl11
    @0
    @1
    @2
    @8
    @14
    @19
    simpl12
    @20
    @2
    @21
    @0
    @1
    @2
    @8
    @14
    @19
    simpl13
    cY
    cZ
    cA
    ssinss1
    #
    syl
    cA
    chlt
    c.pl
    cK
    cX
    @16
    pmodlem.a
    pmodlem.p
    sspadd1
    syl3anc
    @20
    @6
    @9
    cX
    @15
    @19
    simpr
    @10
    @12
    @13
    @3
    @8
    @19
    simpl31
    eqeltrd
    sseldd
    @15
    @6
    @9
    wne
    #
    wa
    #
    cK
    clat
    wcel
    #
    @1
    @21
    @10
    @11
    @16
    wcel
    @6
    cA
    wcel
    #
    @13
    @18
    @24
    @0
    @25
    @0
    @1
    @2
    @8
    @14
    @23
    simpl11
    #
    cK
    hllat
    #
    syl
    @0
    @1
    @2
    @8
    @14
    @23
    simpl12
    #
    @24
    @2
    @21
    @0
    @1
    @2
    @8
    @14
    @23
    simpl13
    #
    @22
    syl
    @10
    @12
    @13
    @3
    @8
    @23
    simpl31
    #
    @24
    cY
    cZ
    @11
    @10
    @12
    @13
    @3
    @8
    @23
    simpl32
    #
    @24
    @0
    @1
    @2
    @4
    @5
    @7
    @10
    @12
    @11
    @9
    @6
    c.or
    co
    c.le
    wbr
    #
    @11
    cZ
    wcel
    @27
    @29
    @30
    @4
    @5
    @7
    @3
    @14
    @23
    simpl21
    #
    @4
    @5
    @7
    @3
    @14
    @23
    simpl22
    @4
    @5
    @7
    @3
    @14
    @23
    simpl23
    #
    @31
    @32
    @24
    @0
    @26
    @11
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    w3a
    #
    @23
    @13
    @33
    @27
    @24
    @26
    @36
    @37
    @24
    cZ
    cA
    @6
    @24
    @0
    @4
    cZ
    cA
    wss
    #
    @27
    @34
    cA
    chlt
    cS
    cK
    cZ
    pmodlem.a
    pmodlem.s
    psubssat
    #
    syl2anc
    @35
    sseldd
    #
    @24
    cY
    cA
    @11
    @30
    @32
    sseldd
    @24
    cX
    cA
    @9
    @29
    @31
    sseldd
    3jca
    @15
    @23
    simpr
    @10
    @12
    @13
    @3
    @8
    @23
    simpl33
    #
    @0
    @38
    @23
    w3a
    @13
    @33
    cA
    @6
    @11
    @9
    c.or
    cK
    c.le
    pmodlem.l
    pmodlem.j
    pmodlem.a
    hlatexch1
    imp
    syl31anc
    @3
    @8
    @10
    @12
    @33
    w3a
    #
    w3a
    #
    @9
    csn
    #
    @6
    csn
    #
    c.pl
    co
    #
    cZ
    @11
    @44
    @45
    cZ
    wss
    #
    @46
    cZ
    wss
    #
    @47
    cZ
    wss
    #
    @44
    @45
    cX
    cZ
    @44
    @9
    cX
    @3
    @8
    @10
    @12
    @33
    simp31
    #
    snssd
    @3
    @4
    @5
    @7
    @43
    simp22
    sstrd
    @44
    @6
    cZ
    @3
    @4
    @5
    @7
    @43
    simp23
    #
    snssd
    @44
    @0
    @45
    cA
    wss
    @46
    cA
    wss
    @4
    @48
    @49
    wa
    @50
    wb
    @0
    @1
    @2
    @8
    @43
    simp11
    #
    @44
    @9
    cA
    @44
    cX
    cA
    @9
    @0
    @1
    @2
    @8
    @43
    simp12
    @51
    sseldd
    #
    snssd
    @44
    @6
    cA
    @44
    cZ
    cA
    @6
    @44
    @0
    @4
    @39
    @53
    @3
    @4
    @5
    @7
    @43
    simp21
    #
    @40
    syl2anc
    @52
    sseldd
    #
    snssd
    @55
    cA
    chlt
    c.pl
    cS
    cK
    @45
    @46
    cZ
    pmodlem.a
    pmodlem.s
    pmodlem.p
    paddss
    syl13anc
    mpbi2and
    @44
    @11
    @47
    wcel
    #
    @33
    @3
    @8
    @10
    @12
    @33
    simp33
    @44
    @25
    @37
    @26
    @36
    @57
    @33
    wb
    @44
    @0
    @25
    @53
    @28
    syl
    @54
    @56
    @44
    cY
    cA
    @11
    @0
    @1
    @2
    @8
    @43
    simp13
    @3
    @8
    @10
    @12
    @33
    simp32
    sseldd
    cA
    c.pl
    @9
    @6
    @11
    c.or
    cK
    c.le
    pmodlem.l
    pmodlem.j
    pmodlem.a
    pmodlem.p
    elpadd2at2
    syl13anc
    mpbird
    sseldd
    syl333anc
    elind
    @41
    @42
    cA
    c.pl
    @9
    @11
    @6
    c.or
    cK
    c.le
    cX
    @16
    pmodlem.l
    pmodlem.j
    pmodlem.a
    pmodlem.p
    elpaddri
    syl322anc
    pm2.61dane
end
