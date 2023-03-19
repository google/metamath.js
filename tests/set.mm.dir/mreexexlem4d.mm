include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "cun.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "cmre.mm"
include "cfv.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wss.mm"
include "simpr.mm"
include "orcd.mm"
include "mreexexlem3d.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "biimpi.mm"
include "adantl.mm"
include "wn.mm"
include "mreexexlem2d.mm"
include "w3a.mm"
include "3anass.mm"
include "cvv.mm"
include "ad2antrr.mm"
include "elfvexd.mm"
include "simpr2.mm"
include "difsnb.mm"
include "sylib.mm"
include "ssdifssd.mm"
include "ssdifd.mm"
include "eqsstr3d.mm"
include "difun1.mm"
include "syl6sseqr.mm"
include "simpr1.mm"
include "uncom.mm"
include "uneq2i.mm"
include "unass.mm"
include "difsnid.mm"
include "uneq1d.mm"
include "syl5eqr.mm"
include "syl5eq.mm"
include "syl.mm"
include "fveq2d.mm"
include "sseqtr4d.mm"
include "simpr3.mm"
include "csuc.mm"
include "wo.mm"
include "com.mm"
include "wi.mm"
include "simplr.mm"
include "3anan12.mm"
include "dif1en.mm"
include "sylbir.mm"
include "expcom.mm"
include "syl2anc.mm"
include "orim12d.mm"
include "mpd.mm"
include "wal.mm"
include "mreexexlemd.mm"
include "simprl.mm"
include "elpwid.mm"
include "difss2d.mm"
include "simplr1.mm"
include "snssd.mm"
include "unssd.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "ssexd.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "ad3antlr.mm"
include "cin.mm"
include "simprrl.mm"
include "vex.mm"
include "en2sn.mm"
include "mp2an.mm"
include "a1i.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "ssdifin0.mm"
include "unen.mm"
include "syl22anc.mm"
include "eqbrtrrd.mm"
include "eqtr2i.mm"
include "simprrr.mm"
include "syl5eqelr.mm"
include "breq2.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "sylan2br.mm"
include "adantlr.mm"
include "exlimddv.mm"
include "pm2.61dane.mm"

theorem mreexexlem4d
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cL: class L
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vi: setvar i
  let vq: setvar q
  let vr: setvar r
  assume mreexexlem2d.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexexlem2d.2: |- N = ( mrCls ` A )
  assume mreexexlem2d.3: |- I = ( mrInd ` A )
  assume mreexexlem2d.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexexlem2d.5: |- ( ph -> F C_ ( X \ H ) )
  assume mreexexlem2d.6: |- ( ph -> G C_ ( X \ H ) )
  assume mreexexlem2d.7: |- ( ph -> F C_ ( N ` ( G u. H ) ) )
  assume mreexexlem2d.8: |- ( ph -> ( F u. H ) e. I )
  assume mreexexlem4d.9: |- ( ph -> L e. _om )
  assume mreexexlem4d.A: |- ( ph -> A. h A. f e. ~P ( X \ h ) A. g e. ~P ( X \ h ) ( ( ( f ~~ L \/ g ~~ L ) /\ f C_ ( N ` ( g u. h ) ) /\ ( f u. h ) e. I ) -> E. j e. ~P g ( f ~~ j /\ ( j u. h ) e. I ) ) )
  assume mreexexlem4d.B: |- ( ph -> ( F ~~ suc L \/ G ~~ suc L ) )

  disjoint f g
  disjoint f h
  disjoint X f
  disjoint g h
  disjoint X g
  disjoint X h
  disjoint I f
  disjoint f j
  disjoint I g
  disjoint g j
  disjoint I h
  disjoint h j
  disjoint I j
  disjoint L f
  disjoint L g
  disjoint L h
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint s y
  disjoint s z
  disjoint N s
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint F s
  disjoint F y
  disjoint F z
  disjoint G s
  disjoint G y
  disjoint G z
  disjoint H s
  disjoint H y
  disjoint H z
  disjoint ph s
  disjoint ph y
  disjoint ph z
  disjoint F j
  disjoint G j
  disjoint H j
  disjoint X s
  disjoint X y
  disjoint f i
  disjoint g i
  disjoint h i
  disjoint I i
  disjoint i j
  disjoint q s
  disjoint q y
  disjoint q z
  disjoint N q
  disjoint q r
  disjoint F q
  disjoint r s
  disjoint F r
  disjoint r y
  disjoint r z
  disjoint G q
  disjoint G r
  disjoint H q
  disjoint H r
  disjoint ph q
  disjoint ph r
  disjoint I q
  disjoint i q
  disjoint j q
  disjoint I r
  disjoint i r
  disjoint j r
  disjoint i ph
  disjoint F i
  disjoint G i
  disjoint H i
  assert |- ( ph -> E. j e. ~P G ( F ~~ j /\ ( j u. H ) e. I ) )

  proof
    wph
    cF
    vj
    cv
    #
    cen
    wbr
    #
    @0
    cH
    cun
    #
    cI
    wcel
    #
    wa
    #
    vj
    cG
    cpw
    #
    wrex
    #
    cF
    c0
    wph
    cF
    c0
    wceq
    #
    wa
    #
    vy
    vz
    cA
    vj
    cF
    cG
    cH
    cI
    cN
    cX
    vs
    wph
    cA
    cX
    cmre
    cfv
    wcel
    #
    @7
    mreexexlem2d.1
    adantr
    mreexexlem2d.2
    mreexexlem2d.3
    wph
    vy
    cv
    #
    vs
    cv
    #
    vz
    cv
    csn
    cun
    cN
    cfv
    wcel
    vz
    @11
    @10
    csn
    cun
    cN
    cfv
    @11
    cN
    cfv
    cdif
    wral
    vy
    cX
    wral
    vs
    cX
    cpw
    wral
    #
    @7
    mreexexlem2d.4
    adantr
    wph
    cF
    cX
    cH
    cdif
    #
    wss
    #
    @7
    mreexexlem2d.5
    adantr
    wph
    cG
    @13
    wss
    #
    @7
    mreexexlem2d.6
    adantr
    wph
    cF
    cG
    cH
    cun
    #
    cN
    cfv
    #
    wss
    #
    @7
    mreexexlem2d.7
    adantr
    wph
    cF
    cH
    cun
    cI
    wcel
    #
    @7
    mreexexlem2d.8
    adantr
    @8
    @7
    cG
    c0
    wceq
    wph
    @7
    simpr
    orcd
    mreexexlem3d
    wph
    cF
    c0
    wne
    #
    wa
    vr
    cv
    #
    cF
    wcel
    #
    @6
    vr
    @20
    @22
    vr
    wex
    #
    wph
    @20
    @23
    vr
    cF
    n0
    biimpi
    adantl
    wph
    @22
    @6
    @20
    wph
    @22
    wa
    #
    vq
    cv
    #
    cF
    @21
    csn
    #
    cdif
    #
    wcel
    wn
    #
    @27
    cH
    @25
    csn
    #
    cun
    #
    cun
    cI
    wcel
    #
    wa
    #
    @6
    vq
    cG
    @24
    vy
    vz
    cA
    vq
    cF
    cG
    cH
    cI
    cN
    cX
    @21
    vs
    wph
    @9
    @22
    mreexexlem2d.1
    adantr
    mreexexlem2d.2
    mreexexlem2d.3
    wph
    @12
    @22
    mreexexlem2d.4
    adantr
    wph
    @14
    @22
    mreexexlem2d.5
    adantr
    wph
    @15
    @22
    mreexexlem2d.6
    adantr
    wph
    @18
    @22
    mreexexlem2d.7
    adantr
    wph
    @19
    @22
    mreexexlem2d.8
    adantr
    wph
    @22
    simpr
    mreexexlem2d
    @25
    cG
    wcel
    #
    @32
    wa
    @24
    @33
    @28
    @31
    w3a
    #
    @6
    @33
    @28
    @31
    3anass
    @24
    @34
    wa
    #
    @27
    vi
    cv
    #
    cen
    wbr
    #
    @36
    @30
    cun
    #
    cI
    wcel
    #
    wa
    #
    @6
    vi
    cG
    @29
    cdif
    #
    cpw
    #
    @35
    vg
    vf
    vh
    vj
    vi
    @27
    @41
    @30
    cI
    cvv
    cL
    cN
    cX
    @35
    cA
    cmre
    cX
    wph
    @9
    @22
    @34
    mreexexlem2d.1
    ad2antrr
    elfvexd
    #
    @35
    @27
    @13
    @29
    cdif
    #
    cX
    @30
    cdif
    #
    @35
    @27
    @27
    @29
    cdif
    #
    @44
    @35
    @28
    @46
    @27
    wceq
    @24
    @33
    @28
    @31
    simpr2
    @25
    @27
    difsnb
    sylib
    @35
    @27
    @13
    @29
    @35
    cF
    @13
    @26
    wph
    @14
    @22
    @34
    mreexexlem2d.5
    ad2antrr
    ssdifssd
    ssdifd
    eqsstr3d
    cX
    cH
    @29
    difun1
    #
    syl6sseqr
    @35
    @41
    @44
    @45
    @35
    cG
    @13
    @29
    wph
    @15
    @22
    @34
    mreexexlem2d.6
    ad2antrr
    ssdifd
    @47
    syl6sseqr
    @35
    cF
    @41
    @30
    cun
    #
    cN
    cfv
    #
    @26
    @35
    cF
    @17
    @49
    wph
    @18
    @22
    @34
    mreexexlem2d.7
    ad2antrr
    @35
    @48
    @16
    cN
    @35
    @33
    @48
    @16
    wceq
    @24
    @33
    @28
    @31
    simpr1
    #
    @33
    @48
    @41
    @29
    cH
    cun
    #
    cun
    #
    @16
    @30
    @51
    @41
    cH
    @29
    uncom
    uneq2i
    @33
    @52
    @41
    @29
    cun
    #
    cH
    cun
    @16
    @41
    @29
    cH
    unass
    @33
    @53
    cG
    cH
    cG
    @25
    difsnid
    uneq1d
    syl5eqr
    syl5eq
    syl
    fveq2d
    sseqtr4d
    ssdifssd
    @24
    @33
    @28
    @31
    simpr3
    @35
    cF
    cL
    csuc
    #
    cen
    wbr
    #
    cG
    @54
    cen
    wbr
    #
    wo
    #
    @27
    cL
    cen
    wbr
    #
    @41
    cL
    cen
    wbr
    #
    wo
    wph
    @57
    @22
    @34
    mreexexlem4d.B
    ad2antrr
    @35
    @55
    @58
    @56
    @59
    @35
    cL
    com
    wcel
    #
    @22
    @55
    @58
    wi
    wph
    @60
    @22
    @34
    mreexexlem4d.9
    ad2antrr
    #
    wph
    @22
    @34
    simplr
    @55
    @60
    @22
    wa
    #
    @58
    @55
    @62
    wa
    @60
    @55
    @22
    w3a
    @58
    @60
    @55
    @22
    3anan12
    cF
    cL
    @21
    dif1en
    sylbir
    expcom
    syl2anc
    @35
    @60
    @33
    @56
    @59
    wi
    @61
    @50
    @56
    @60
    @33
    wa
    #
    @59
    @56
    @63
    wa
    @60
    @56
    @33
    w3a
    @59
    @60
    @56
    @33
    3anan12
    cG
    cL
    @25
    dif1en
    sylbir
    expcom
    syl2anc
    orim12d
    mpd
    wph
    vf
    cv
    #
    cL
    cen
    wbr
    vg
    cv
    #
    cL
    cen
    wbr
    wo
    @64
    @65
    vh
    cv
    #
    cun
    cN
    cfv
    wss
    @64
    @66
    cun
    cI
    wcel
    w3a
    @64
    @0
    cen
    wbr
    @0
    @66
    cun
    cI
    wcel
    wa
    vj
    @65
    cpw
    wrex
    wi
    vg
    cX
    @66
    cdif
    cpw
    #
    wral
    vf
    @67
    wral
    vh
    wal
    @22
    @34
    mreexexlem4d.A
    ad2antrr
    mreexexlemd
    @35
    @36
    @42
    wcel
    #
    @40
    wa
    #
    wa
    #
    @36
    @29
    cun
    #
    @5
    wcel
    #
    cF
    @71
    cen
    wbr
    #
    @71
    cH
    cun
    #
    cI
    wcel
    #
    @6
    @70
    @72
    @71
    cG
    wss
    #
    @70
    @36
    @29
    cG
    @70
    @36
    cG
    @29
    @70
    @36
    @41
    @35
    @68
    @40
    simprl
    elpwid
    #
    difss2d
    @70
    @25
    cG
    @33
    @28
    @31
    @24
    @69
    simplr1
    snssd
    unssd
    @70
    cG
    cvv
    wcel
    @72
    @76
    wb
    @70
    cG
    cX
    cvv
    @35
    cX
    cvv
    wcel
    @69
    @43
    adantr
    @70
    cG
    cX
    cH
    wph
    @15
    @22
    @34
    @69
    mreexexlem2d.6
    ad3antrrr
    difss2d
    ssexd
    @71
    cG
    cvv
    elpw2g
    syl
    mpbird
    @70
    @27
    @26
    cun
    #
    cF
    @71
    cen
    @22
    @78
    cF
    wceq
    wph
    @34
    @69
    cF
    @21
    difsnid
    ad3antlr
    @70
    @37
    @26
    @29
    cen
    wbr
    #
    @27
    @26
    cin
    #
    c0
    wceq
    #
    @36
    @29
    cin
    c0
    wceq
    #
    @78
    @71
    cen
    wbr
    @35
    @68
    @37
    @39
    simprrl
    @79
    @70
    @21
    cvv
    wcel
    @25
    cvv
    wcel
    @79
    vr
    vex
    vq
    vex
    @21
    @25
    cvv
    cvv
    en2sn
    mp2an
    a1i
    @81
    @70
    @80
    @26
    @27
    cin
    c0
    @27
    @26
    incom
    @26
    cF
    disjdif
    eqtri
    a1i
    @70
    @36
    @41
    wss
    @82
    @77
    @36
    cG
    @29
    ssdifin0
    syl
    @27
    @36
    @26
    @29
    unen
    syl22anc
    eqbrtrrd
    @70
    @74
    @38
    cI
    @74
    @36
    @51
    cun
    @38
    @36
    @29
    cH
    unass
    @51
    @30
    @36
    @29
    cH
    uncom
    uneq2i
    eqtr2i
    @35
    @68
    @37
    @39
    simprrr
    syl5eqelr
    @4
    @73
    @75
    wa
    vj
    @71
    @5
    @0
    @71
    wceq
    #
    @1
    @73
    @3
    @75
    @0
    @71
    cF
    cen
    breq2
    @83
    @2
    @74
    cI
    @0
    @71
    cH
    uneq1
    eleq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    sylan2br
    rexlimddv
    adantlr
    exlimddv
    pm2.61dane
end
