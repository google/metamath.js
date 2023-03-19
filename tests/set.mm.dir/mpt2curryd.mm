include "ccur.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wbr.mm"
include "copab.mm"
include "cmpt.mm"
include "df-cur.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "dmmpt2ga.mm"
include "syl.mm"
include "dmeqd.mm"
include "c0.mm"
include "wne.mm"
include "dmxp.mm"
include "eqtrd.mm"
include "mpteq1d.mm"
include "wa.mm"
include "df-mpt.mm"
include "cfv.mm"
include "wfun.mm"
include "wb.mm"
include "mpt2fun.mm"
include "funbrfv2b.mm"
include "mp1i.mm"
include "adantr.mm"
include "eleq2d.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "an32.mm"
include "ancom.mm"
include "bitri.mm"
include "ibar.mm"
include "bicomd.mm"
include "adantl.mm"
include "co.mm"
include "df-ov.mm"
include "csb.mm"
include "cmpt2.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcsb.mm"
include "weq.mm"
include "csbeq1a.mm"
include "sylan9eq.mm"
include "cbvmpt2.mm"
include "eqtri.mm"
include "a1i.mm"
include "eqcomd.mm"
include "equcoms.mm"
include "csbeq2dv.mm"
include "simpr.mm"
include "wi.mm"
include "rsp2.mm"
include "impl.mm"
include "ovmpt2d.mm"
include "syl5eqr.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "3bitrrd.mm"
include "opabbidv.mm"
include "syl5req.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"

theorem mpt2curryd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  assume mpt2curryd.f: |- F = ( x e. X , y e. Y |-> C )
  assume mpt2curryd.c: |- ( ph -> A. x e. X A. y e. Y C e. V )
  assume mpt2curryd.n: |- ( ph -> Y =/= (/) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint C a
  disjoint C b
  disjoint a b
  disjoint C z
  disjoint F z
  disjoint x z
  disjoint y z
  disjoint V z
  disjoint X a
  disjoint X b
  disjoint X z
  disjoint Y a
  disjoint Y b
  disjoint Y z
  disjoint a ph
  disjoint b ph
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint ph z
  assert |- ( ph -> curry F = ( x e. X |-> ( y e. Y |-> C ) ) )

  proof
    wph
    cF
    ccur
    vx
    cF
    cdm
    #
    cdm
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cF
    wbr
    #
    vy
    vz
    copab
    #
    cmpt
    #
    vx
    cX
    vy
    cY
    cC
    cmpt
    #
    cmpt
    #
    vx
    vy
    vz
    cF
    df-cur
    wph
    @8
    vx
    cX
    @7
    cmpt
    @10
    wph
    vx
    @1
    cX
    @7
    wph
    @1
    cX
    cY
    cxp
    #
    cdm
    #
    cX
    wph
    @0
    @11
    wph
    cC
    cV
    wcel
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @0
    @11
    wceq
    #
    mpt2curryd.c
    vx
    vy
    cX
    cY
    cC
    cF
    cV
    mpt2curryd.f
    dmmpt2ga
    syl
    #
    dmeqd
    wph
    cY
    c0
    wne
    @12
    cX
    wceq
    mpt2curryd.n
    cX
    cY
    dmxp
    syl
    eqtrd
    mpteq1d
    wph
    vx
    cX
    @7
    @9
    wph
    @2
    cX
    wcel
    #
    wa
    #
    @9
    @3
    cY
    wcel
    #
    @5
    cC
    wceq
    #
    wa
    #
    vy
    vz
    copab
    @7
    vy
    vz
    cY
    cC
    df-mpt
    @18
    @21
    @6
    vy
    vz
    @18
    @6
    @4
    @0
    wcel
    #
    @4
    cF
    cfv
    #
    @5
    wceq
    #
    wa
    #
    @17
    @19
    wa
    #
    @24
    wa
    #
    @21
    cF
    wfun
    @6
    @25
    wb
    @18
    vx
    vy
    cX
    cY
    cC
    cF
    mpt2curryd.f
    mpt2fun
    @4
    @5
    cF
    funbrfv2b
    mp1i
    @18
    @22
    @26
    @24
    @18
    @22
    @4
    @11
    wcel
    @26
    @18
    @0
    @11
    @4
    wph
    @15
    @17
    @16
    adantr
    eleq2d
    @2
    @3
    cX
    cY
    opelxp
    syl6bb
    anbi1d
    @27
    @19
    @17
    @24
    wa
    #
    wa
    #
    @18
    @21
    @27
    @28
    @19
    wa
    @29
    @17
    @19
    @24
    an32
    @28
    @19
    ancom
    bitri
    @18
    @19
    @28
    @20
    @18
    @19
    wa
    #
    @28
    @24
    @20
    @18
    @28
    @24
    wb
    #
    @19
    @17
    @31
    wph
    @17
    @24
    @28
    @17
    @24
    ibar
    bicomd
    adantl
    adantr
    @30
    @24
    cC
    @5
    wceq
    @20
    @30
    @23
    cC
    @5
    @30
    @23
    @2
    @3
    cF
    co
    cC
    @2
    @3
    cF
    df-ov
    @30
    va
    vb
    @2
    @3
    cX
    cY
    vy
    vb
    cv
    #
    vx
    va
    cv
    #
    cC
    csb
    #
    csb
    #
    cC
    cF
    cV
    cF
    va
    vb
    cX
    cY
    @35
    cmpt2
    #
    wceq
    @30
    cF
    vx
    vy
    cX
    cY
    cC
    cmpt2
    @36
    mpt2curryd.f
    vx
    vy
    va
    vb
    cX
    cY
    cC
    @35
    va
    cC
    nfcv
    vb
    cC
    nfcv
    vx
    vy
    @32
    @34
    vx
    @32
    nfcv
    vx
    @33
    cC
    nfcsb1v
    nfcsb
    vy
    @32
    @34
    nfcsb1v
    vx
    va
    weq
    #
    vy
    vb
    weq
    #
    cC
    @34
    @35
    vx
    @33
    cC
    csbeq1a
    #
    vy
    @32
    @34
    csbeq1a
    sylan9eq
    cbvmpt2
    eqtri
    a1i
    va
    vx
    weq
    #
    vb
    vy
    weq
    #
    wa
    @35
    cC
    wceq
    @30
    @40
    @41
    @35
    vy
    @32
    cC
    csb
    #
    cC
    @40
    vy
    @32
    @34
    cC
    @34
    cC
    wceq
    vx
    va
    @37
    cC
    @34
    @39
    eqcomd
    equcoms
    csbeq2dv
    @42
    cC
    wceq
    vy
    vb
    @38
    cC
    @42
    vy
    @32
    cC
    csbeq1a
    eqcomd
    equcoms
    sylan9eq
    adantl
    @18
    @17
    @19
    wph
    @17
    simpr
    adantr
    @18
    @19
    simpr
    wph
    @17
    @19
    @13
    wph
    @14
    @26
    @13
    wi
    mpt2curryd.c
    @13
    vx
    vy
    cX
    cY
    rsp2
    syl
    impl
    ovmpt2d
    syl5eqr
    eqeq1d
    cC
    @5
    eqcom
    syl6bb
    bitrd
    pm5.32da
    syl5bb
    3bitrrd
    opabbidv
    syl5req
    mpteq2dva
    eqtrd
    syl5eq
end
