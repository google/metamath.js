include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cres.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "cxr.mm"
include "cle.mm"
include "iccssxr.mm"
include "simplrl.mm"
include "sseldi.mm"
include "simplrr.mm"
include "cr.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "simpr.mm"
include "ltled.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "fvres.mm"
include "syl.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "cv.mm"
include "cdv.mm"
include "cioo.mm"
include "wrex.mm"
include "ccncf.mm"
include "iccss2.mm"
include "ad2antlr.mm"
include "rescncf.mm"
include "sylc.mm"
include "wf.mm"
include "cdm.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp2d.mm"
include "iooss1.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
include "fssresd.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "cc.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cncff.mm"
include "fss.mm"
include "sylancl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "iccntr.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fdm.mm"
include "mvth.mm"
include "ffvelrnda.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "eqeltrrd.mm"

theorem dvgt0lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  assume dvgt0.a: |- ( ph -> A e. RR )
  assume dvgt0.b: |- ( ph -> B e. RR )
  assume dvgt0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvgt0lem.d: |- ( ph -> ( RR _D F ) : ( A (,) B ) --> S )


  assert |- ( ( ( ph /\ ( X e. ( A [,] B ) /\ Y e. ( A [,] B ) ) ) /\ X < Y ) -> ( ( ( F ` Y ) - ( F ` X ) ) / ( Y - X ) ) e. S )

  proof
    wph
    cX
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cY
    @0
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    clt
    wbr
    #
    wa
    #
    cY
    cF
    cX
    cY
    cicc
    co
    #
    cres
    #
    cfv
    #
    cX
    @8
    cfv
    #
    cmin
    co
    #
    cY
    cX
    cmin
    co
    #
    cdiv
    co
    #
    cY
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cmin
    co
    #
    @12
    cdiv
    co
    cS
    @6
    @11
    @16
    @12
    cdiv
    @6
    @9
    @14
    @10
    @15
    cmin
    @6
    cY
    @7
    wcel
    #
    @9
    @14
    wceq
    @6
    cX
    cxr
    wcel
    #
    cY
    cxr
    wcel
    #
    cX
    cY
    cle
    wbr
    #
    @17
    @6
    @0
    cxr
    cX
    cA
    cB
    iccssxr
    #
    wph
    @1
    @2
    @5
    simplrl
    #
    sseldi
    #
    @6
    @0
    cxr
    cY
    @21
    wph
    @1
    @2
    @5
    simplrr
    #
    sseldi
    #
    @6
    cX
    cY
    @6
    @0
    cr
    cX
    wph
    @0
    cr
    wss
    #
    @3
    @5
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @26
    dvgt0.a
    dvgt0.b
    cA
    cB
    iccssre
    syl2anc
    ad2antrr
    #
    @22
    sseldd
    #
    @6
    @0
    cr
    cY
    @29
    @24
    sseldd
    #
    @4
    @5
    simpr
    #
    ltled
    #
    cX
    cY
    ubicc2
    syl3anc
    cY
    @7
    cF
    fvres
    syl
    @6
    cX
    @7
    wcel
    #
    @10
    @15
    wceq
    @6
    @18
    @19
    @20
    @34
    @23
    @25
    @33
    cX
    cY
    lbicc2
    syl3anc
    cX
    @7
    cF
    fvres
    syl
    oveq12d
    oveq1d
    @6
    vz
    cv
    #
    cr
    @8
    cdv
    co
    #
    cfv
    #
    @13
    wceq
    #
    vz
    cX
    cY
    cioo
    co
    #
    wrex
    @13
    cS
    wcel
    #
    @6
    vz
    cX
    cY
    @8
    @30
    @31
    @32
    @6
    @7
    @0
    wss
    #
    cF
    @0
    cr
    ccncf
    co
    wcel
    #
    @8
    @7
    cr
    ccncf
    co
    wcel
    @3
    @41
    wph
    @5
    cA
    cB
    cX
    cY
    iccss2
    ad2antlr
    wph
    @42
    @3
    @5
    dvgt0.f
    ad2antrr
    @0
    cr
    @7
    cF
    rescncf
    sylc
    @6
    @39
    cS
    @36
    wf
    #
    @36
    cdm
    @39
    wceq
    @6
    @43
    @39
    cS
    cr
    cF
    cdv
    co
    #
    @39
    cres
    #
    wf
    @6
    cA
    cB
    cioo
    co
    #
    cS
    @39
    @44
    wph
    @46
    cS
    @44
    wf
    @3
    @5
    dvgt0lem.d
    ad2antrr
    @6
    @39
    cA
    cY
    cioo
    co
    #
    @46
    @6
    cA
    cxr
    wcel
    cA
    cX
    cle
    wbr
    #
    @39
    @47
    wss
    @6
    cA
    wph
    @27
    @3
    @5
    dvgt0.a
    ad2antrr
    #
    rexrd
    @6
    cX
    cr
    wcel
    #
    @48
    cX
    cB
    cle
    wbr
    #
    @6
    @1
    @50
    @48
    @51
    w3a
    #
    @22
    @6
    @27
    @28
    @1
    @52
    wb
    @49
    wph
    @28
    @3
    @5
    dvgt0.b
    ad2antrr
    #
    cA
    cB
    cX
    elicc2
    syl2anc
    mpbid
    simp2d
    cA
    cX
    cY
    iooss1
    syl2anc
    @6
    cB
    cxr
    wcel
    cY
    cB
    cle
    wbr
    #
    @47
    @46
    wss
    @6
    cB
    @53
    rexrd
    @6
    cY
    cr
    wcel
    #
    cA
    cY
    cle
    wbr
    #
    @54
    @6
    @2
    @55
    @56
    @54
    w3a
    #
    @24
    @6
    @27
    @28
    @2
    @57
    wb
    @49
    @53
    cA
    cB
    cY
    elicc2
    syl2anc
    mpbid
    simp3d
    cA
    cY
    cB
    iooss2
    syl2anc
    sstrd
    fssresd
    @6
    @39
    cS
    @36
    @45
    @6
    @36
    @44
    @7
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @45
    @6
    cr
    cc
    wss
    #
    @0
    cc
    cF
    wf
    #
    @26
    @7
    cr
    wss
    #
    @36
    @60
    wceq
    @61
    @6
    ax-resscn
    a1i
    @6
    @0
    cr
    cF
    wf
    #
    @61
    @62
    wph
    @64
    @3
    @5
    wph
    @42
    @64
    dvgt0.f
    @0
    cr
    cF
    cncff
    syl
    ad2antrr
    ax-resscn
    @0
    cr
    cc
    cF
    fss
    sylancl
    @29
    @6
    @50
    @55
    @63
    @30
    @31
    cX
    cY
    iccssre
    syl2anc
    @0
    @7
    cr
    @58
    cF
    ccnfld
    ctopn
    cfv
    #
    @65
    eqid
    #
    @65
    @66
    tgioo2
    dvres
    syl22anc
    @6
    @59
    @39
    @44
    @6
    @50
    @55
    @59
    @39
    wceq
    @30
    @31
    cX
    cY
    iccntr
    syl2anc
    reseq2d
    eqtrd
    feq1d
    mpbird
    #
    @39
    cS
    @36
    fdm
    syl
    mvth
    @6
    @38
    @40
    vz
    @39
    @6
    @35
    @39
    wcel
    wa
    @37
    cS
    wcel
    @38
    @40
    @6
    @39
    cS
    @35
    @36
    @67
    ffvelrnda
    @37
    @13
    cS
    eleq1
    syl5ibcom
    rexlimdva
    mpd
    eqeltrrd
end
