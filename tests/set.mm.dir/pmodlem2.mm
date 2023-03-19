include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "simpl22.mm"
include "padd02.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "ineq1d.mm"
include "ssinss1.mm"
include "syl.mm"
include "simpl21.mm"
include "sspadd2.mm"
include "syl3anc.mm"
include "eqsstrd.mm"
include "oveq2.mm"
include "simp1.mm"
include "simp21.mm"
include "padd01.mm"
include "sylan9eqr.mm"
include "inss1.mm"
include "sspadd1.mm"
include "syl5ss.mm"
include "wne.mm"
include "cv.mm"
include "elin.mm"
include "wi.mm"
include "wbr.mm"
include "wrex.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "simprl.mm"
include "elpaddn0.mm"
include "syl31anc.mm"
include "simpl23.mm"
include "simpl3.mm"
include "simpr1.mm"
include "simpr2l.mm"
include "simpr2r.mm"
include "simpr3.mm"
include "pmodlem1.mm"
include "syl333anc.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdvv.mm"
include "adantld.mm"
include "adantrl.mm"
include "sylbid.mm"
include "exp32.mm"
include "com34.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "pm2.61da2ne.mm"

theorem pmodlem2
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pmodlem.l: |- .<_ = ( le ` K )
  assume pmodlem.j: |- .\/ = ( join ` K )
  assume pmodlem.a: |- A = ( Atoms ` K )
  assume pmodlem.s: |- S = ( PSubSp ` K )
  assume pmodlem.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z e. S ) /\ X C_ Z ) -> ( ( X .+ Y ) i^i Z ) C_ ( X .+ ( Y i^i Z ) ) )

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
    cZ
    cS
    wcel
    #
    w3a
    #
    cX
    cZ
    wss
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    cin
    #
    cX
    cY
    cZ
    cin
    #
    c.pl
    co
    #
    wss
    cX
    c0
    cY
    c0
    @6
    cX
    c0
    wceq
    #
    wa
    #
    @8
    @9
    @10
    @12
    @7
    cY
    cZ
    @12
    @7
    c0
    cY
    c.pl
    co
    #
    cY
    @12
    cX
    c0
    cY
    c.pl
    @6
    @11
    simpr
    oveq1d
    @12
    @0
    @2
    @13
    cY
    wceq
    @0
    @4
    @5
    @11
    simpl1
    #
    @1
    @2
    @3
    @0
    @5
    @11
    simpl22
    #
    cA
    chlt
    c.pl
    cK
    cY
    pmodlem.a
    pmodlem.p
    padd02
    syl2anc
    eqtrd
    ineq1d
    @12
    @0
    @9
    cA
    wss
    #
    @1
    @9
    @10
    wss
    @14
    @12
    @2
    @16
    @15
    cY
    cZ
    cA
    ssinss1
    #
    syl
    @1
    @2
    @3
    @0
    @5
    @11
    simpl21
    cA
    chlt
    c.pl
    cK
    @9
    cX
    pmodlem.a
    pmodlem.p
    sspadd2
    syl3anc
    eqsstrd
    @6
    cY
    c0
    wceq
    #
    wa
    #
    @8
    cX
    cZ
    cin
    #
    @10
    @19
    @7
    cX
    cZ
    @18
    @6
    @7
    cX
    c0
    c.pl
    co
    #
    cX
    cY
    c0
    cX
    c.pl
    oveq2
    @6
    @0
    @1
    @21
    cX
    wceq
    @0
    @4
    @5
    simp1
    @0
    @1
    @2
    @3
    @5
    simp21
    cA
    chlt
    c.pl
    cK
    cX
    pmodlem.a
    pmodlem.p
    padd01
    syl2anc
    sylan9eqr
    ineq1d
    @19
    @20
    cX
    @10
    cX
    cZ
    inss1
    @19
    @0
    @1
    @16
    cX
    @10
    wss
    @0
    @4
    @5
    @18
    simpl1
    @1
    @2
    @3
    @0
    @5
    @18
    simpl21
    @19
    @2
    @16
    @1
    @2
    @3
    @0
    @5
    @18
    simpl22
    @17
    syl
    cA
    chlt
    c.pl
    cK
    cX
    @9
    pmodlem.a
    pmodlem.p
    sspadd1
    syl3anc
    syl5ss
    eqsstrd
    @6
    cX
    c0
    wne
    cY
    c0
    wne
    wa
    #
    wa
    #
    vp
    @8
    @10
    vp
    cv
    #
    @8
    wcel
    @24
    @7
    wcel
    #
    @24
    cZ
    wcel
    #
    wa
    @23
    @24
    @10
    wcel
    #
    @24
    @7
    cZ
    elin
    @6
    @22
    @25
    @26
    @27
    @6
    @22
    @26
    @25
    @27
    @6
    @22
    @26
    @25
    @27
    wi
    @6
    @22
    @26
    wa
    #
    wa
    #
    @25
    @24
    cA
    wcel
    #
    @24
    vq
    cv
    #
    vr
    cv
    #
    c.or
    co
    c.le
    wbr
    #
    vr
    cY
    wrex
    vq
    cX
    wrex
    #
    wa
    #
    @27
    @29
    cK
    clat
    wcel
    #
    @1
    @2
    @22
    @25
    @35
    wb
    @29
    @0
    @36
    @0
    @4
    @5
    @28
    simpl1
    cK
    hllat
    syl
    @1
    @2
    @3
    @0
    @5
    @28
    simpl21
    @1
    @2
    @3
    @0
    @5
    @28
    simpl22
    @6
    @22
    @26
    simprl
    cA
    c.pl
    @24
    c.or
    cK
    c.le
    cX
    cY
    vr
    vq
    pmodlem.l
    pmodlem.j
    pmodlem.a
    pmodlem.p
    elpaddn0
    syl31anc
    @6
    @26
    @35
    @27
    wi
    @22
    @6
    @26
    wa
    #
    @34
    @27
    @30
    @37
    @33
    @27
    vq
    vr
    cX
    cY
    @6
    @26
    @31
    cX
    wcel
    #
    @32
    cY
    wcel
    #
    wa
    #
    @33
    @27
    wi
    wi
    @6
    @26
    @40
    @33
    @27
    @6
    @26
    @40
    @33
    w3a
    #
    wa
    @0
    @1
    @2
    @3
    @5
    @26
    @38
    @39
    @33
    @27
    @0
    @4
    @5
    @41
    simpl1
    @1
    @2
    @3
    @0
    @5
    @41
    simpl21
    @1
    @2
    @3
    @0
    @5
    @41
    simpl22
    @1
    @2
    @3
    @0
    @5
    @41
    simpl23
    @0
    @4
    @5
    @41
    simpl3
    @6
    @26
    @40
    @33
    simpr1
    @38
    @39
    @26
    @33
    @6
    simpr2l
    @38
    @39
    @26
    @33
    @6
    simpr2r
    @6
    @26
    @40
    @33
    simpr3
    cA
    c.pl
    cS
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vr
    vq
    vp
    pmodlem.l
    pmodlem.j
    pmodlem.a
    pmodlem.s
    pmodlem.p
    pmodlem1
    syl333anc
    3exp2
    imp
    rexlimdvv
    adantld
    adantrl
    sylbid
    exp32
    com34
    imp4b
    syl5bi
    ssrdv
    pm2.61da2ne
end
