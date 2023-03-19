include "cvv.mm"
include "ccrd.mm"
include "cfv.mm"
include "cin.mm"
include "cmre.mm"
include "elfvexd.mm"
include "wceq.mm"
include "wo.mm"
include "cen.mm"
include "wbr.mm"
include "word.mm"
include "cardon.mm"
include "onordi.mm"
include "ordtri2or3.mm"
include "mp2an.mm"
include "difss2d.mm"
include "ssexd.mm"
include "cardidd.mm"
include "ensymd.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "orim12d.mm"
include "mpi.mm"
include "com.mm"
include "wcel.mm"
include "cv.mm"
include "cun.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "wi.mm"
include "cdif.mm"
include "wral.mm"
include "wal.mm"
include "cfn.mm"
include "ficardom.mm"
include "orim12i.mm"
include "syl.mm"
include "wb.mm"
include "ordom.mm"
include "ordelinel.mm"
include "mp3an.mm"
include "sylibr.mm"
include "c0.mm"
include "csuc.mm"
include "orbi12d.mm"
include "3anbi1d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "albidv.mm"
include "imbi2d.mm"
include "ad2antrr.mm"
include "csn.mm"
include "simplrl.mm"
include "elpwid.mm"
include "simplrr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpr1.mm"
include "en0.mm"
include "orbi12i.mm"
include "sylib.mm"
include "mreexexlem3d.mm"
include "ex.mm"
include "ralrimivva.mm"
include "alrimiv.mm"
include "nfv.mm"
include "nfa1.mm"
include "nf3an.mm"
include "nfra1.mm"
include "nfal.mm"
include "nfra2.mm"
include "nfan.mm"
include "3ad2ant1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "mreexexlem4d.mm"
include "expr.mm"
include "ralrimi.mm"
include "alrimi.mm"
include "3exp.mm"
include "com12.mm"
include "a2d.mm"
include "finds.mm"
include "mpcom.mm"
include "mreexexlemd.mm"

theorem mreexexdOLD
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vq: setvar q
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vl: setvar l
  let vk: setvar k
  let vi: setvar i
  assume mreexexlem2d.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexexlem2d.2: |- N = ( mrCls ` A )
  assume mreexexlem2d.3: |- I = ( mrInd ` A )
  assume mreexexlem2d.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexexlem2d.5: |- ( ph -> F C_ ( X \ H ) )
  assume mreexexlem2d.6: |- ( ph -> G C_ ( X \ H ) )
  assume mreexexlem2d.7: |- ( ph -> F C_ ( N ` ( G u. H ) ) )
  assume mreexexlem2d.8: |- ( ph -> ( F u. H ) e. I )
  assume mreexexd.9: |- ( ph -> ( F e. Fin \/ G e. Fin ) )

  disjoint F q
  disjoint G q
  disjoint X s
  disjoint s y
  disjoint s z
  disjoint X y
  disjoint X z
  disjoint y z
  disjoint ph s
  disjoint ph y
  disjoint ph z
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint ph q
  disjoint I q
  disjoint H q
  disjoint f q
  disjoint g q
  disjoint h q
  disjoint F f
  disjoint f g
  disjoint f h
  disjoint F g
  disjoint F h
  disjoint g h
  disjoint f l
  disjoint F l
  disjoint g l
  disjoint h l
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G l
  disjoint f s
  disjoint g s
  disjoint h s
  disjoint k s
  disjoint X f
  disjoint f y
  disjoint f z
  disjoint f k
  disjoint X g
  disjoint g y
  disjoint g z
  disjoint g k
  disjoint X h
  disjoint h y
  disjoint h z
  disjoint h k
  disjoint X k
  disjoint k y
  disjoint k z
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint i s
  disjoint I f
  disjoint f i
  disjoint I g
  disjoint g i
  disjoint I h
  disjoint h i
  disjoint i y
  disjoint I i
  disjoint I k
  disjoint i z
  disjoint i k
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint N k
  disjoint X l
  disjoint k l
  disjoint l ph
  disjoint I l
  disjoint i l
  disjoint N l
  disjoint i q
  assert |- ( ph -> E. q e. ~P G ( F ~~ q /\ ( q u. H ) e. I ) )

  proof
    wph
    vg
    vf
    vh
    vi
    vq
    cF
    cG
    cH
    cI
    cvv
    cF
    ccrd
    cfv
    #
    cG
    ccrd
    cfv
    #
    cin
    #
    cN
    cX
    wph
    cA
    cmre
    cX
    mreexexlem2d.1
    elfvexd
    #
    mreexexlem2d.5
    mreexexlem2d.6
    mreexexlem2d.7
    mreexexlem2d.8
    wph
    @0
    @2
    wceq
    #
    @1
    @2
    wceq
    #
    wo
    #
    cF
    @2
    cen
    wbr
    #
    cG
    @2
    cen
    wbr
    #
    wo
    @0
    word
    #
    @1
    word
    #
    @6
    @0
    cF
    cardon
    onordi
    #
    @1
    cG
    cardon
    onordi
    #
    @0
    @1
    ordtri2or3
    mp2an
    wph
    @4
    @7
    @5
    @8
    wph
    cF
    @0
    cen
    wbr
    @4
    @7
    wph
    @0
    cF
    wph
    cF
    cvv
    wph
    cF
    cX
    cvv
    @3
    wph
    cF
    cX
    cH
    mreexexlem2d.5
    difss2d
    ssexd
    cardidd
    ensymd
    @0
    @2
    cF
    cen
    breq2
    syl5ibcom
    wph
    cG
    @1
    cen
    wbr
    @5
    @8
    wph
    @1
    cG
    wph
    cG
    cvv
    wph
    cG
    cX
    cvv
    @3
    wph
    cG
    cX
    cH
    mreexexlem2d.6
    difss2d
    ssexd
    cardidd
    ensymd
    @1
    @2
    cG
    cen
    breq2
    syl5ibcom
    orim12d
    mpi
    @2
    com
    wcel
    #
    wph
    vf
    cv
    #
    @2
    cen
    wbr
    #
    vg
    cv
    #
    @2
    cen
    wbr
    #
    wo
    #
    @14
    @16
    vh
    cv
    #
    cun
    cN
    cfv
    wss
    #
    @14
    @19
    cun
    cI
    wcel
    #
    w3a
    #
    @14
    vi
    cv
    #
    cen
    wbr
    @23
    @19
    cun
    cI
    wcel
    wa
    vi
    @16
    cpw
    wrex
    #
    wi
    #
    vg
    cX
    @19
    cdif
    #
    cpw
    #
    wral
    vf
    @27
    wral
    #
    vh
    wal
    #
    wph
    @0
    com
    wcel
    #
    @1
    com
    wcel
    #
    wo
    #
    @13
    wph
    cF
    cfn
    wcel
    #
    cG
    cfn
    wcel
    #
    wo
    @32
    mreexexd.9
    @33
    @30
    @34
    @31
    cF
    ficardom
    cG
    ficardom
    orim12i
    syl
    @9
    @10
    com
    word
    @13
    @32
    wb
    @11
    @12
    ordom
    @0
    @1
    com
    ordelinel
    mp3an
    sylibr
    wph
    @14
    vl
    cv
    #
    cen
    wbr
    #
    @16
    @35
    cen
    wbr
    #
    wo
    #
    @20
    @21
    w3a
    #
    @24
    wi
    #
    vg
    @27
    wral
    vf
    @27
    wral
    #
    vh
    wal
    #
    wi
    wph
    @14
    c0
    cen
    wbr
    #
    @16
    c0
    cen
    wbr
    #
    wo
    #
    @20
    @21
    w3a
    #
    @24
    wi
    #
    vg
    @27
    wral
    vf
    @27
    wral
    #
    vh
    wal
    #
    wi
    wph
    @14
    vk
    cv
    #
    cen
    wbr
    #
    @16
    @50
    cen
    wbr
    #
    wo
    #
    @20
    @21
    w3a
    #
    @24
    wi
    #
    vg
    @27
    wral
    #
    vf
    @27
    wral
    #
    vh
    wal
    #
    wi
    wph
    @14
    @50
    csuc
    #
    cen
    wbr
    #
    @16
    @59
    cen
    wbr
    #
    wo
    #
    @20
    @21
    w3a
    #
    @24
    wi
    #
    vg
    @27
    wral
    #
    vf
    @27
    wral
    #
    vh
    wal
    #
    wi
    wph
    @29
    wi
    vl
    vk
    @2
    @35
    c0
    wceq
    #
    @42
    @49
    wph
    @68
    @41
    @48
    vh
    @68
    @40
    @47
    vf
    vg
    @27
    @27
    @68
    @39
    @46
    @24
    @68
    @38
    @45
    @20
    @21
    @68
    @36
    @43
    @37
    @44
    @35
    c0
    @14
    cen
    breq2
    @35
    c0
    @16
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    @35
    @50
    wceq
    #
    @42
    @58
    wph
    @69
    @41
    @57
    vh
    @69
    @40
    @55
    vf
    vg
    @27
    @27
    @69
    @39
    @54
    @24
    @69
    @38
    @53
    @20
    @21
    @69
    @36
    @51
    @37
    @52
    @35
    @50
    @14
    cen
    breq2
    @35
    @50
    @16
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    @35
    @59
    wceq
    #
    @42
    @67
    wph
    @70
    @41
    @66
    vh
    @70
    @40
    @64
    vf
    vg
    @27
    @27
    @70
    @39
    @63
    @24
    @70
    @38
    @62
    @20
    @21
    @70
    @36
    @60
    @37
    @61
    @35
    @59
    @14
    cen
    breq2
    @35
    @59
    @16
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    @35
    @2
    wceq
    #
    @42
    @29
    wph
    @71
    @41
    @28
    vh
    @71
    @40
    @25
    vf
    vg
    @27
    @27
    @71
    @39
    @22
    @24
    @71
    @38
    @18
    @20
    @21
    @71
    @36
    @15
    @37
    @17
    @35
    @2
    @14
    cen
    breq2
    @35
    @2
    @16
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    wph
    @48
    vh
    wph
    @47
    vf
    vg
    @27
    @27
    wph
    @14
    @27
    wcel
    #
    @16
    @27
    wcel
    #
    wa
    #
    wa
    #
    @46
    @24
    @75
    @46
    wa
    #
    vy
    vz
    cA
    vi
    @14
    @16
    @19
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
    @74
    @46
    mreexexlem2d.1
    ad2antrr
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
    @79
    @78
    csn
    cun
    cN
    cfv
    @79
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
    @74
    @46
    mreexexlem2d.4
    ad2antrr
    @76
    @14
    @26
    wph
    @72
    @73
    @46
    simplrl
    elpwid
    @76
    @16
    @26
    wph
    @72
    @73
    @46
    simplrr
    elpwid
    @75
    @45
    @20
    @21
    simpr2
    @75
    @45
    @20
    @21
    simpr3
    @76
    @45
    @14
    c0
    wceq
    #
    @16
    c0
    wceq
    #
    wo
    @75
    @45
    @20
    @21
    simpr1
    @43
    @81
    @44
    @82
    @14
    en0
    @16
    en0
    orbi12i
    sylib
    mreexexlem3d
    ex
    ralrimivva
    alrimiv
    @50
    com
    wcel
    #
    wph
    @58
    @67
    wph
    @83
    @58
    @67
    wi
    wph
    @83
    @58
    @67
    wph
    @83
    @58
    w3a
    #
    @66
    vh
    wph
    @83
    @58
    vh
    wph
    vh
    nfv
    @83
    vh
    nfv
    @57
    vh
    nfa1
    nf3an
    @84
    @65
    vf
    @27
    wph
    @83
    @58
    vf
    wph
    vf
    nfv
    @83
    vf
    nfv
    @57
    vf
    vh
    @56
    vf
    @27
    nfra1
    nfal
    nf3an
    @84
    @72
    @65
    @84
    @72
    wa
    @64
    vg
    @27
    @84
    @72
    vg
    wph
    @83
    @58
    vg
    wph
    vg
    nfv
    @83
    vg
    nfv
    @57
    vg
    vh
    @55
    vf
    vg
    @27
    @27
    nfra2
    nfal
    nf3an
    @72
    vg
    nfv
    nfan
    @84
    @72
    @73
    @64
    @84
    @74
    wa
    #
    @63
    @24
    @85
    @63
    wa
    #
    vy
    vz
    cA
    vf
    vg
    vh
    vi
    @14
    @16
    @19
    cI
    @50
    cN
    cX
    vs
    @84
    @77
    @74
    @63
    wph
    @83
    @77
    @58
    mreexexlem2d.1
    3ad2ant1
    ad2antrr
    mreexexlem2d.2
    mreexexlem2d.3
    @84
    @80
    @74
    @63
    wph
    @83
    @80
    @58
    mreexexlem2d.4
    3ad2ant1
    ad2antrr
    @86
    @14
    @26
    @84
    @72
    @73
    @63
    simplrl
    elpwid
    @86
    @16
    @26
    @84
    @72
    @73
    @63
    simplrr
    elpwid
    @85
    @62
    @20
    @21
    simpr2
    @85
    @62
    @20
    @21
    simpr3
    wph
    @83
    @58
    @74
    @63
    simpll2
    wph
    @83
    @58
    @74
    @63
    simpll3
    @85
    @62
    @20
    @21
    simpr1
    mreexexlem4d
    ex
    expr
    ralrimi
    ex
    ralrimi
    alrimi
    3exp
    com12
    a2d
    finds
    mpcom
    mreexexlemd
end
