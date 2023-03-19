include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "wb.mm"
include "simp23.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1.mm"
include "eqid.mm"
include "llnbase.mm"
include "syl.mm"
include "islln3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp3r.mm"
include "necomd.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "clat.mm"
include "simp11.mm"
include "hllat.mm"
include "simp2l.mm"
include "atbase.mm"
include "simp2r.mm"
include "simp121.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "simp3.mm"
include "llni2.mm"
include "syl31anc.mm"
include "llncmp.mm"
include "syl3anc.mm"
include "bitr2d.mm"
include "necon3abid.mm"
include "ianor.mm"
include "syl6bb.mm"
include "simpl11.mm"
include "adantr.mm"
include "simp122.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpr.mm"
include "simp13l.mm"
include "llnexchb2lem.mm"
include "syl331anc.mm"
include "ex.mm"
include "hlatjcom.mm"
include "breq2d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "3bitr4d.mm"
include "jaod.mm"
include "sylbid.mm"
include "neeq1.mm"
include "breq2.mm"
include "oveq2.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "3exp.mm"
include "imp4a.mm"
include "rexlimdvv.mm"
include "mp2d.mm"

theorem llnexchb2
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  assume llnexch.l: |- .<_ = ( le ` K )
  assume llnexch.j: |- .\/ = ( join ` K )
  assume llnexch.m: |- ./\ = ( meet ` K )
  assume llnexch.a: |- A = ( Atoms ` K )
  assume llnexch.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ ( X e. N /\ Y e. N /\ Z e. N ) /\ ( ( X ./\ Y ) e. A /\ X =/= Z ) ) -> ( ( X ./\ Y ) .<_ Z <-> ( X ./\ Y ) = ( X ./\ Z ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    cZ
    cN
    wcel
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cA
    wcel
    #
    cX
    cZ
    wne
    #
    wa
    #
    w3a
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cZ
    @10
    @11
    c.or
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    #
    cZ
    cX
    wne
    #
    @5
    cZ
    c.le
    wbr
    #
    @5
    cX
    cZ
    c.an
    co
    #
    wceq
    #
    wb
    #
    @9
    @3
    @16
    @0
    @1
    @2
    @3
    @8
    simp23
    #
    @9
    @0
    cZ
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    @16
    wb
    @0
    @4
    @8
    simp1
    @9
    @3
    @24
    @22
    @23
    cK
    cN
    cZ
    @23
    eqid
    #
    llnexch.n
    llnbase
    syl
    cA
    @23
    c.or
    cK
    cN
    cZ
    vq
    vp
    @25
    llnexch.j
    llnexch.a
    llnexch.n
    islln3
    syl2anc
    mpbid
    @9
    cX
    cZ
    @0
    @4
    @6
    @7
    simp3r
    necomd
    @9
    @15
    @17
    @21
    wi
    #
    vp
    vq
    cA
    cA
    @9
    @10
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    wa
    #
    @12
    @14
    @26
    @9
    @29
    @12
    @14
    @26
    wi
    @9
    @29
    @12
    w3a
    #
    @26
    @14
    @13
    cX
    wne
    #
    @5
    @13
    c.le
    wbr
    #
    @5
    cX
    @13
    c.an
    co
    #
    wceq
    #
    wb
    #
    wi
    @30
    @31
    @10
    cX
    c.le
    wbr
    #
    wn
    #
    @11
    cX
    c.le
    wbr
    #
    wn
    #
    wo
    #
    @35
    @30
    @31
    @36
    @38
    wa
    #
    wn
    @40
    @30
    @41
    @13
    cX
    @30
    @41
    @13
    cX
    c.le
    wbr
    #
    @13
    cX
    wceq
    #
    @30
    cK
    clat
    wcel
    #
    @10
    @23
    wcel
    #
    @11
    @23
    wcel
    #
    cX
    @23
    wcel
    #
    @41
    @42
    wb
    @30
    @0
    @44
    @0
    @4
    @8
    @29
    @12
    simp11
    #
    cK
    hllat
    syl
    @30
    @27
    @45
    @9
    @27
    @28
    @12
    simp2l
    #
    cA
    @23
    @10
    cK
    @25
    llnexch.a
    atbase
    syl
    @30
    @28
    @46
    @9
    @27
    @28
    @12
    simp2r
    #
    cA
    @23
    @11
    cK
    @25
    llnexch.a
    atbase
    syl
    @30
    @1
    @47
    @1
    @2
    @3
    @0
    @8
    @29
    @12
    simp121
    #
    @23
    cK
    cN
    cX
    @25
    llnexch.n
    llnbase
    syl
    @23
    c.or
    cK
    c.le
    @10
    @11
    cX
    @25
    llnexch.l
    llnexch.j
    latjle12
    syl13anc
    @30
    @0
    @13
    cN
    wcel
    #
    @1
    @42
    @43
    wb
    @48
    @30
    @0
    @27
    @28
    @12
    @52
    @48
    @49
    @50
    @9
    @29
    @12
    simp3
    cA
    @10
    @11
    c.or
    cK
    cN
    llnexch.j
    llnexch.a
    llnexch.n
    llni2
    syl31anc
    @51
    cK
    c.le
    cN
    @13
    cX
    llnexch.l
    llnexch.n
    llncmp
    syl3anc
    bitr2d
    necon3abid
    @36
    @38
    ianor
    syl6bb
    @30
    @37
    @35
    @39
    @30
    @37
    @35
    @30
    @37
    wa
    @0
    @1
    @2
    @27
    @28
    @37
    @6
    @35
    @0
    @4
    @8
    @29
    @12
    @37
    simpl11
    @30
    @1
    @37
    @51
    adantr
    @30
    @2
    @37
    @1
    @2
    @3
    @0
    @8
    @29
    @12
    simp122
    #
    adantr
    @27
    @28
    @9
    @12
    @37
    simpl2l
    @27
    @28
    @9
    @12
    @37
    simpl2r
    @30
    @37
    simpr
    @30
    @6
    @37
    @6
    @7
    @0
    @4
    @29
    @12
    simp13l
    #
    adantr
    cA
    @10
    @11
    c.or
    cK
    c.le
    c.an
    cN
    cX
    cY
    llnexch.l
    llnexch.j
    llnexch.m
    llnexch.a
    llnexch.n
    llnexchb2lem
    syl331anc
    ex
    @30
    @39
    @35
    @30
    @39
    wa
    #
    @5
    @11
    @10
    c.or
    co
    #
    c.le
    wbr
    #
    @5
    cX
    @56
    c.an
    co
    #
    wceq
    #
    @32
    @34
    @55
    @0
    @1
    @2
    @28
    @27
    @39
    @6
    @57
    @59
    wb
    @0
    @4
    @8
    @29
    @12
    @39
    simpl11
    #
    @30
    @1
    @39
    @51
    adantr
    @30
    @2
    @39
    @53
    adantr
    @27
    @28
    @9
    @12
    @39
    simpl2r
    #
    @27
    @28
    @9
    @12
    @39
    simpl2l
    #
    @30
    @39
    simpr
    @30
    @6
    @39
    @54
    adantr
    cA
    @11
    @10
    c.or
    cK
    c.le
    c.an
    cN
    cX
    cY
    llnexch.l
    llnexch.j
    llnexch.m
    llnexch.a
    llnexch.n
    llnexchb2lem
    syl331anc
    @55
    @13
    @56
    @5
    c.le
    @55
    @0
    @27
    @28
    @13
    @56
    wceq
    @60
    @62
    @61
    cA
    c.or
    cK
    @10
    @11
    llnexch.j
    llnexch.a
    hlatjcom
    syl3anc
    #
    breq2d
    @55
    @33
    @58
    @5
    @55
    @13
    @56
    cX
    c.an
    @63
    oveq2d
    eqeq2d
    3bitr4d
    ex
    jaod
    sylbid
    @14
    @17
    @31
    @21
    @35
    cZ
    @13
    cX
    neeq1
    @14
    @18
    @32
    @20
    @34
    cZ
    @13
    @5
    c.le
    breq2
    @14
    @19
    @33
    @5
    cZ
    @13
    cX
    c.an
    oveq2
    eqeq2d
    bibi12d
    imbi12d
    syl5ibrcom
    3exp
    imp4a
    rexlimdvv
    mp2d
end
