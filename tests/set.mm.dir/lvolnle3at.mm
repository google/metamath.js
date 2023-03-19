include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "clpl.mm"
include "wrex.mm"
include "co.mm"
include "wn.mm"
include "cbs.mm"
include "simplr.mm"
include "wb.mm"
include "eqid.mm"
include "islvol.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "notbid.mm"
include "wne.mm"
include "simp1l.mm"
include "simp3l.mm"
include "simp21.mm"
include "simp22.mm"
include "lplnnle2at.mm"
include "syl13anc.mm"
include "cplt.mm"
include "lplnbase.mm"
include "syl.mm"
include "simp1r.mm"
include "lvolbase.mm"
include "simp3r.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "pltletr.mm"
include "mpand.mm"
include "pltle.mm"
include "syld.mm"
include "mtod.mm"
include "adantr.mm"
include "simprr.mm"
include "clat.mm"
include "hllat.mm"
include "simp23.mm"
include "atbase.mm"
include "latleeqj2.mm"
include "mtbird.mm"
include "anassrs.mm"
include "simpl1l.mm"
include "simpl3l.mm"
include "simpl2.mm"
include "simpr.mm"
include "lplni2.mm"
include "lplnnlt.mm"
include "latjcl.mm"
include "pm2.61dan.mm"
include "cple.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "pm2.61ne.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem lvolnle3at
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume lvolnle3at.l: |- .<_ = ( le ` K )
  assume lvolnle3at.j: |- .\/ = ( join ` K )
  assume lvolnle3at.a: |- A = ( Atoms ` K )
  assume lvolnle3at.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. HL /\ X e. V ) /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> -. X .<_ ( ( P .\/ Q ) .\/ R ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    wa
    #
    vy
    cv
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vy
    cK
    clpl
    cfv
    #
    wrex
    #
    cX
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
    #
    wn
    #
    @7
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @12
    @7
    @1
    @18
    @12
    wa
    #
    @0
    @1
    @6
    simplr
    @0
    @1
    @19
    wb
    @1
    @6
    vy
    chlt
    @17
    @9
    @11
    cK
    cV
    cX
    @17
    eqid
    #
    @9
    eqid
    #
    @11
    eqid
    #
    lvolnle3at.v
    islvol
    ad2antrr
    mpbid
    simprd
    @7
    @10
    @16
    vy
    @11
    @7
    @8
    @11
    wcel
    #
    @10
    @16
    @2
    @6
    @23
    @10
    wa
    #
    @16
    @2
    @6
    @24
    w3a
    #
    @16
    cX
    cQ
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
    #
    wn
    cP
    cQ
    cP
    cQ
    wceq
    #
    @15
    @28
    @29
    @14
    @27
    cX
    c.le
    @29
    @13
    @26
    cR
    c.or
    cP
    cQ
    cQ
    c.or
    oveq1
    oveq1d
    breq2d
    notbid
    @25
    cP
    cQ
    wne
    #
    wa
    cR
    @13
    c.le
    wbr
    #
    @16
    @25
    @30
    @31
    @16
    @25
    @30
    @31
    wa
    #
    wa
    #
    @15
    cX
    @13
    c.le
    wbr
    #
    @25
    @34
    wn
    @32
    @25
    @34
    @8
    @13
    c.le
    wbr
    #
    @25
    @0
    @23
    @3
    @4
    @35
    wn
    @0
    @1
    @6
    @24
    simp1l
    #
    @2
    @6
    @23
    @10
    simp3l
    #
    @2
    @3
    @4
    @5
    @24
    simp21
    #
    @2
    @3
    @4
    @5
    @24
    simp22
    #
    cA
    @11
    cP
    cQ
    c.or
    cK
    c.le
    @8
    lvolnle3at.l
    lvolnle3at.j
    lvolnle3at.a
    @22
    lplnnle2at
    syl13anc
    @25
    @34
    @8
    @13
    cK
    cplt
    cfv
    #
    wbr
    #
    @35
    @25
    @8
    cX
    @40
    wbr
    #
    @34
    @41
    @25
    @0
    @8
    @17
    wcel
    #
    @18
    @10
    @42
    @36
    @25
    @23
    @43
    @37
    @17
    @11
    cK
    @8
    @20
    @22
    lplnbase
    syl
    #
    @25
    @1
    @18
    @0
    @1
    @6
    @24
    simp1r
    @17
    cK
    cV
    cX
    @20
    lvolnle3at.v
    lvolbase
    syl
    #
    @2
    @6
    @23
    @10
    simp3r
    chlt
    @17
    @9
    @40
    cK
    @8
    cX
    @20
    @40
    eqid
    #
    @21
    cvrlt
    syl31anc
    #
    @25
    cK
    cpo
    wcel
    #
    @43
    @18
    @13
    @17
    wcel
    #
    @42
    @34
    wa
    @41
    wi
    @25
    @0
    @48
    @36
    cK
    hlpos
    syl
    #
    @44
    @45
    @25
    @0
    @3
    @4
    @49
    @36
    @38
    @39
    cA
    @17
    c.or
    cK
    cP
    cQ
    @20
    lvolnle3at.j
    lvolnle3at.a
    hlatjcl
    syl3anc
    #
    @17
    @40
    cK
    c.le
    @8
    cX
    @13
    @20
    lvolnle3at.l
    @46
    pltletr
    syl13anc
    mpand
    @25
    @0
    @23
    @49
    @41
    @35
    wi
    @36
    @37
    @51
    chlt
    @11
    @17
    @40
    cK
    c.le
    @8
    @13
    lvolnle3at.l
    @46
    pltle
    syl3anc
    syld
    mtod
    adantr
    @33
    @14
    @13
    cX
    c.le
    @33
    @31
    @14
    @13
    wceq
    #
    @25
    @30
    @31
    simprr
    @25
    @31
    @52
    wb
    #
    @32
    @25
    cK
    clat
    wcel
    #
    cR
    @17
    wcel
    #
    @49
    @53
    @25
    @0
    @54
    @36
    cK
    hllat
    syl
    #
    @25
    @5
    @55
    @2
    @3
    @4
    @5
    @24
    simp23
    #
    cA
    @17
    cR
    cK
    @20
    lvolnle3at.a
    atbase
    syl
    #
    @51
    @17
    c.or
    cK
    c.le
    cR
    @13
    @20
    lvolnle3at.l
    lvolnle3at.j
    latleeqj2
    syl3anc
    adantr
    mpbid
    breq2d
    mtbird
    anassrs
    @25
    @30
    @31
    wn
    #
    @16
    @25
    @30
    @59
    wa
    #
    wa
    #
    @15
    @8
    @14
    @40
    wbr
    #
    @61
    @0
    @23
    @14
    @11
    wcel
    #
    @62
    wn
    @0
    @1
    @6
    @24
    @60
    simpl1l
    #
    @23
    @10
    @2
    @6
    @60
    simpl3l
    @61
    @0
    @6
    @60
    @63
    @64
    @2
    @6
    @24
    @60
    simpl2
    @25
    @60
    simpr
    cA
    @11
    cP
    cQ
    cR
    c.or
    cK
    c.le
    lvolnle3at.l
    lvolnle3at.j
    lvolnle3at.a
    @22
    lplni2
    syl3anc
    @11
    @40
    cK
    @8
    @14
    @46
    @22
    lplnnlt
    syl3anc
    @25
    @15
    @62
    wi
    @60
    @25
    @42
    @15
    @62
    @47
    @25
    @48
    @43
    @18
    @14
    @17
    wcel
    #
    @42
    @15
    wa
    @62
    wi
    @50
    @44
    @45
    @25
    @54
    @49
    @55
    @65
    @56
    @51
    @58
    @17
    c.or
    cK
    @13
    cR
    @20
    lvolnle3at.j
    latjcl
    syl3anc
    @17
    @40
    cK
    c.le
    @8
    cX
    @14
    @20
    lvolnle3at.l
    @46
    pltletr
    syl13anc
    mpand
    adantr
    mtod
    anassrs
    pm2.61dan
    @25
    @28
    cX
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    @25
    @67
    @8
    @66
    cK
    cple
    cfv
    #
    wbr
    #
    @25
    @0
    @23
    @4
    @5
    @69
    wn
    @36
    @37
    @39
    @57
    cA
    @11
    cQ
    cR
    c.or
    cK
    @68
    @8
    @68
    eqid
    #
    lvolnle3at.j
    lvolnle3at.a
    @22
    lplnnle2at
    syl13anc
    @25
    @67
    @8
    @66
    @40
    wbr
    #
    @69
    @25
    @42
    @67
    @71
    @47
    @25
    @48
    @43
    @18
    @66
    @17
    wcel
    #
    @42
    @67
    wa
    @71
    wi
    @50
    @44
    @45
    @25
    @0
    @4
    @5
    @72
    @36
    @39
    @57
    cA
    @17
    c.or
    cK
    cQ
    cR
    @20
    lvolnle3at.j
    lvolnle3at.a
    hlatjcl
    syl3anc
    #
    @17
    @40
    cK
    c.le
    @8
    cX
    @66
    @20
    lvolnle3at.l
    @46
    pltletr
    syl13anc
    mpand
    @25
    @0
    @23
    @72
    @71
    @69
    wi
    @36
    @37
    @73
    chlt
    @11
    @17
    @40
    cK
    @68
    @8
    @66
    @70
    @46
    pltle
    syl3anc
    syld
    mtod
    @25
    @27
    @66
    cX
    c.le
    @25
    @26
    cQ
    cR
    c.or
    @25
    @0
    @4
    @26
    cQ
    wceq
    @36
    @39
    cA
    c.or
    cK
    cQ
    lvolnle3at.j
    lvolnle3at.a
    hlatjidm
    syl2anc
    oveq1d
    breq2d
    mtbird
    pm2.61ne
    3expia
    expd
    rexlimdv
    mpd
end
