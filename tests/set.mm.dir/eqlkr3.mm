include "wf.mm"
include "wfn.mm"
include "clvec.mm"
include "wcel.mm"
include "lflf.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "cur.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "eqid.mm"
include "eqlkr.mm"
include "syl121anc.mm"
include "wi.mm"
include "adantr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "cinvr.mm"
include "simpr.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "cdr.mm"
include "wne.mm"
include "lvecdrng.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "drnginvrl.mm"
include "crg.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lmodring.mm"
include "drnginvrcl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "syld.mm"
include "ancrd.mm"
include "reximdva.mm"
include "mpd.mm"
include "wb.mm"
include "ringidcl.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "ceqsrexv.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "ringridm.mm"
include "eqfnfvd.mm"

theorem eqlkr3
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  assume eqlkr3.v: |- V = ( Base ` W )
  assume eqlkr3.s: |- S = ( Scalar ` W )
  assume eqlkr3.r: |- R = ( Base ` S )
  assume eqlkr3.o: |- .0. = ( 0g ` S )
  assume eqlkr3.f: |- F = ( LFnl ` W )
  assume eqlkr3.k: |- K = ( LKer ` W )
  assume eqlkr3.w: |- ( ph -> W e. LVec )
  assume eqlkr3.x: |- ( ph -> X e. V )
  assume eqlkr3.g: |- ( ph -> G e. F )
  assume eqlkr3.h: |- ( ph -> H e. F )
  assume eqlkr3.e: |- ( ph -> ( K ` G ) = ( K ` H ) )
  assume eqlkr3.a: |- ( ph -> ( G ` X ) = ( H ` X ) )
  assume eqlkr3.n: |- ( ph -> ( G ` X ) =/= .0. )


  assert |- ( ph -> G = H )

  proof
    wph
    vx
    cV
    cG
    cH
    wph
    cV
    cR
    cG
    wf
    #
    cG
    cV
    wfn
    wph
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    @0
    eqlkr3.w
    eqlkr3.g
    cS
    cF
    cG
    cR
    cV
    cW
    clvec
    eqlkr3.s
    eqlkr3.r
    eqlkr3.v
    eqlkr3.f
    lflf
    syl2anc
    cV
    cR
    cG
    ffn
    syl
    wph
    cV
    cR
    cH
    wf
    #
    cH
    cV
    wfn
    wph
    @1
    cH
    cF
    wcel
    #
    @3
    eqlkr3.w
    eqlkr3.h
    cS
    cF
    cH
    cR
    cV
    cW
    clvec
    eqlkr3.s
    eqlkr3.r
    eqlkr3.v
    eqlkr3.f
    lflf
    syl2anc
    cV
    cR
    cH
    ffn
    syl
    wph
    vx
    cv
    #
    cV
    wcel
    #
    wa
    #
    @5
    cH
    cfv
    #
    @5
    cG
    cfv
    #
    cS
    cur
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @9
    wph
    @8
    @12
    wceq
    #
    vx
    cV
    wph
    vr
    cv
    #
    @10
    wceq
    #
    @8
    @9
    @14
    @11
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    wa
    #
    vr
    cR
    wrex
    #
    @13
    vx
    cV
    wral
    #
    wph
    @18
    vr
    cR
    wrex
    #
    @20
    wph
    @1
    @2
    @4
    cG
    cK
    cfv
    cH
    cK
    cfv
    wceq
    @22
    eqlkr3.w
    eqlkr3.g
    eqlkr3.h
    eqlkr3.e
    vx
    cS
    @11
    cF
    cG
    cH
    cR
    cK
    cV
    cW
    vr
    eqlkr3.s
    eqlkr3.r
    @11
    eqid
    #
    eqlkr3.v
    eqlkr3.f
    eqlkr3.k
    eqlkr
    syl121anc
    wph
    @18
    @19
    vr
    cR
    wph
    @14
    cR
    wcel
    #
    wa
    #
    @18
    @15
    @25
    @18
    cX
    cH
    cfv
    #
    cX
    cG
    cfv
    #
    @14
    @11
    co
    #
    wceq
    #
    @15
    @25
    cX
    cV
    wcel
    #
    @18
    @29
    wi
    wph
    @30
    @24
    eqlkr3.x
    adantr
    @17
    @29
    vx
    cX
    cV
    @5
    cX
    wceq
    #
    @8
    @26
    @16
    @28
    @5
    cX
    cH
    fveq2
    @31
    @9
    @27
    @14
    @11
    @5
    cX
    cG
    fveq2
    oveq1d
    eqeq12d
    rspcv
    syl
    @25
    @29
    @15
    @25
    @29
    wa
    #
    @27
    cS
    cinvr
    cfv
    #
    cfv
    #
    @28
    @11
    co
    #
    @34
    @27
    @11
    co
    #
    @14
    @10
    @32
    @28
    @27
    @34
    @11
    @32
    @27
    @26
    @28
    @25
    @27
    @26
    wceq
    #
    @29
    wph
    @37
    @24
    eqlkr3.a
    adantr
    adantr
    @25
    @29
    simpr
    eqtr2d
    oveq2d
    @25
    @35
    @14
    wceq
    @29
    @25
    @36
    @14
    @11
    co
    #
    @10
    @14
    @11
    co
    #
    @35
    @14
    @25
    @36
    @10
    @14
    @11
    @25
    cS
    cdr
    wcel
    #
    @27
    cR
    wcel
    #
    @27
    c.0
    wne
    #
    @36
    @10
    wceq
    #
    wph
    @40
    @24
    wph
    @1
    @40
    eqlkr3.w
    cS
    cW
    eqlkr3.s
    lvecdrng
    syl
    adantr
    #
    wph
    @41
    @24
    wph
    @1
    @2
    @30
    @41
    eqlkr3.w
    eqlkr3.g
    eqlkr3.x
    cS
    cF
    cG
    cR
    cV
    cW
    cX
    clvec
    eqlkr3.s
    eqlkr3.r
    eqlkr3.v
    eqlkr3.f
    lflcl
    syl3anc
    adantr
    #
    wph
    @42
    @24
    eqlkr3.n
    adantr
    #
    cR
    cS
    @11
    @10
    @33
    @27
    c.0
    eqlkr3.r
    eqlkr3.o
    @23
    @10
    eqid
    #
    @33
    eqid
    #
    drnginvrl
    syl3anc
    #
    oveq1d
    @25
    cS
    crg
    wcel
    #
    @34
    cR
    wcel
    #
    @41
    @24
    @38
    @35
    wceq
    wph
    @50
    @24
    wph
    cW
    clmod
    wcel
    #
    @50
    wph
    @1
    @52
    eqlkr3.w
    cW
    lveclmod
    syl
    #
    cS
    cW
    eqlkr3.s
    lmodring
    #
    syl
    #
    adantr
    #
    @25
    @40
    @41
    @42
    @51
    @44
    @45
    @46
    cR
    cS
    @33
    @27
    c.0
    eqlkr3.r
    eqlkr3.o
    @48
    drnginvrcl
    syl3anc
    @45
    wph
    @24
    simpr
    #
    cR
    cS
    @11
    @34
    @27
    @14
    eqlkr3.r
    @23
    ringass
    syl13anc
    @25
    @50
    @24
    @39
    @14
    wceq
    @56
    @57
    cR
    cS
    @11
    @10
    @14
    eqlkr3.r
    @23
    @47
    ringlidm
    syl2anc
    3eqtr3d
    adantr
    @25
    @43
    @29
    @49
    adantr
    3eqtr3d
    ex
    syld
    ancrd
    reximdva
    mpd
    wph
    @10
    cR
    wcel
    #
    @20
    @21
    wb
    wph
    @50
    @58
    @55
    cR
    cS
    @10
    eqlkr3.r
    @47
    ringidcl
    syl
    @18
    @21
    vr
    @10
    cR
    @15
    @17
    @13
    vx
    cV
    @15
    @16
    @12
    @8
    @14
    @10
    @9
    @11
    oveq2
    eqeq2d
    ralbidv
    ceqsrexv
    syl
    mpbid
    r19.21bi
    @7
    @50
    @9
    cR
    wcel
    #
    @12
    @9
    wceq
    @7
    @52
    @50
    wph
    @52
    @6
    @53
    adantr
    @54
    syl
    @7
    @1
    @2
    @6
    @59
    wph
    @1
    @6
    eqlkr3.w
    adantr
    wph
    @2
    @6
    eqlkr3.g
    adantr
    wph
    @6
    simpr
    cS
    cF
    cG
    cR
    cV
    cW
    @5
    clvec
    eqlkr3.s
    eqlkr3.r
    eqlkr3.v
    eqlkr3.f
    lflcl
    syl3anc
    cR
    cS
    @11
    @10
    @9
    eqlkr3.r
    @23
    @47
    ringridm
    syl2anc
    eqtr2d
    eqfnfvd
end
