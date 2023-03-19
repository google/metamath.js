include "cvv.mm"
include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cif.mm"
include "cmre.mm"
include "elfvexd.mm"
include "wn.mm"
include "wo.mm"
include "cen.mm"
include "wbr.mm"
include "exmid.mm"
include "wi.mm"
include "ficardid.mm"
include "ensymd.mm"
include "iftrue.mm"
include "breqtrrd.mm"
include "a1i.mm"
include "wa.mm"
include "orcanai.mm"
include "syl.mm"
include "wceq.mm"
include "iffalse.mm"
include "adantl.mm"
include "ex.mm"
include "orim12d.mm"
include "mpi.mm"
include "com.mm"
include "cv.mm"
include "cun.mm"
include "wss.mm"
include "w3a.mm"
include "cpw.mm"
include "wrex.mm"
include "cdif.mm"
include "wral.mm"
include "wal.mm"
include "ficardom.mm"
include "ifclda.mm"
include "c0.mm"
include "csuc.mm"
include "breq2.mm"
include "orbi12d.mm"
include "3anbi1d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "albidv.mm"
include "imbi2d.mm"
include "weq.mm"
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

theorem mreexexd
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
    cfn
    wcel
    #
    cF
    ccrd
    cfv
    #
    cG
    ccrd
    cfv
    #
    cif
    #
    cN
    cX
    wph
    cA
    cmre
    cX
    mreexexlem2d.1
    elfvexd
    mreexexlem2d.5
    mreexexlem2d.6
    mreexexlem2d.7
    mreexexlem2d.8
    wph
    @0
    @0
    wn
    #
    wo
    cF
    @3
    cen
    wbr
    #
    cG
    @3
    cen
    wbr
    #
    wo
    @0
    exmid
    wph
    @0
    @5
    @4
    @6
    @0
    @5
    wi
    wph
    @0
    cF
    @1
    @3
    cen
    @0
    @1
    cF
    cF
    ficardid
    ensymd
    @0
    @1
    @2
    iftrue
    breqtrrd
    a1i
    wph
    @4
    @6
    wph
    @4
    wa
    #
    cG
    @2
    @3
    cen
    @7
    cG
    cfn
    wcel
    #
    cG
    @2
    cen
    wbr
    wph
    @0
    @8
    mreexexd.9
    orcanai
    #
    @8
    @2
    cG
    cG
    ficardid
    ensymd
    syl
    @4
    @3
    @2
    wceq
    wph
    @0
    @1
    @2
    iffalse
    adantl
    breqtrrd
    ex
    orim12d
    mpi
    @3
    com
    wcel
    wph
    vf
    cv
    #
    @3
    cen
    wbr
    #
    vg
    cv
    #
    @3
    cen
    wbr
    #
    wo
    #
    @10
    @12
    vh
    cv
    #
    cun
    cN
    cfv
    wss
    #
    @10
    @15
    cun
    cI
    wcel
    #
    w3a
    #
    @10
    vi
    cv
    #
    cen
    wbr
    @19
    @15
    cun
    cI
    wcel
    wa
    vi
    @12
    cpw
    wrex
    #
    wi
    #
    vg
    cX
    @15
    cdif
    #
    cpw
    #
    wral
    vf
    @23
    wral
    #
    vh
    wal
    #
    wph
    @0
    @1
    @2
    com
    @0
    @1
    com
    wcel
    wph
    cF
    ficardom
    adantl
    @7
    @8
    @2
    com
    wcel
    @9
    cG
    ficardom
    syl
    ifclda
    wph
    @10
    vl
    cv
    #
    cen
    wbr
    #
    @12
    @26
    cen
    wbr
    #
    wo
    #
    @16
    @17
    w3a
    #
    @20
    wi
    #
    vg
    @23
    wral
    vf
    @23
    wral
    #
    vh
    wal
    #
    wi
    wph
    @10
    c0
    cen
    wbr
    #
    @12
    c0
    cen
    wbr
    #
    wo
    #
    @16
    @17
    w3a
    #
    @20
    wi
    #
    vg
    @23
    wral
    vf
    @23
    wral
    #
    vh
    wal
    #
    wi
    wph
    @10
    vk
    cv
    #
    cen
    wbr
    #
    @12
    @41
    cen
    wbr
    #
    wo
    #
    @16
    @17
    w3a
    #
    @20
    wi
    #
    vg
    @23
    wral
    #
    vf
    @23
    wral
    #
    vh
    wal
    #
    wi
    wph
    @10
    @41
    csuc
    #
    cen
    wbr
    #
    @12
    @50
    cen
    wbr
    #
    wo
    #
    @16
    @17
    w3a
    #
    @20
    wi
    #
    vg
    @23
    wral
    #
    vf
    @23
    wral
    #
    vh
    wal
    #
    wi
    wph
    @25
    wi
    vl
    vk
    @3
    @26
    c0
    wceq
    #
    @33
    @40
    wph
    @59
    @32
    @39
    vh
    @59
    @31
    @38
    vf
    vg
    @23
    @23
    @59
    @30
    @37
    @20
    @59
    @29
    @36
    @16
    @17
    @59
    @27
    @34
    @28
    @35
    @26
    c0
    @10
    cen
    breq2
    @26
    c0
    @12
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    vl
    vk
    weq
    #
    @33
    @49
    wph
    @60
    @32
    @48
    vh
    @60
    @31
    @46
    vf
    vg
    @23
    @23
    @60
    @30
    @45
    @20
    @60
    @29
    @44
    @16
    @17
    @60
    @27
    @42
    @28
    @43
    @26
    @41
    @10
    cen
    breq2
    @26
    @41
    @12
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    @26
    @50
    wceq
    #
    @33
    @58
    wph
    @61
    @32
    @57
    vh
    @61
    @31
    @55
    vf
    vg
    @23
    @23
    @61
    @30
    @54
    @20
    @61
    @29
    @53
    @16
    @17
    @61
    @27
    @51
    @28
    @52
    @26
    @50
    @10
    cen
    breq2
    @26
    @50
    @12
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    @26
    @3
    wceq
    #
    @33
    @25
    wph
    @62
    @32
    @24
    vh
    @62
    @31
    @21
    vf
    vg
    @23
    @23
    @62
    @30
    @18
    @20
    @62
    @29
    @14
    @16
    @17
    @62
    @27
    @11
    @28
    @13
    @26
    @3
    @10
    cen
    breq2
    @26
    @3
    @12
    cen
    breq2
    orbi12d
    3anbi1d
    imbi1d
    2ralbidv
    albidv
    imbi2d
    wph
    @39
    vh
    wph
    @38
    vf
    vg
    @23
    @23
    wph
    @10
    @23
    wcel
    #
    @12
    @23
    wcel
    #
    wa
    #
    wa
    #
    @37
    @20
    @66
    @37
    wa
    #
    vy
    vz
    cA
    vi
    @10
    @12
    @15
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
    @65
    @37
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
    @70
    @69
    csn
    cun
    cN
    cfv
    @70
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
    @65
    @37
    mreexexlem2d.4
    ad2antrr
    @67
    @10
    @22
    wph
    @63
    @64
    @37
    simplrl
    elpwid
    @67
    @12
    @22
    wph
    @63
    @64
    @37
    simplrr
    elpwid
    @66
    @36
    @16
    @17
    simpr2
    @66
    @36
    @16
    @17
    simpr3
    @67
    @36
    @10
    c0
    wceq
    #
    @12
    c0
    wceq
    #
    wo
    @66
    @36
    @16
    @17
    simpr1
    @34
    @72
    @35
    @73
    @10
    en0
    @12
    en0
    orbi12i
    sylib
    mreexexlem3d
    ex
    ralrimivva
    alrimiv
    @41
    com
    wcel
    #
    wph
    @49
    @58
    wph
    @74
    @49
    @58
    wi
    wph
    @74
    @49
    @58
    wph
    @74
    @49
    w3a
    #
    @57
    vh
    wph
    @74
    @49
    vh
    wph
    vh
    nfv
    @74
    vh
    nfv
    @48
    vh
    nfa1
    nf3an
    @75
    @56
    vf
    @23
    wph
    @74
    @49
    vf
    wph
    vf
    nfv
    @74
    vf
    nfv
    @48
    vf
    vh
    @47
    vf
    @23
    nfra1
    nfal
    nf3an
    @75
    @63
    @56
    @75
    @63
    wa
    @55
    vg
    @23
    @75
    @63
    vg
    wph
    @74
    @49
    vg
    wph
    vg
    nfv
    @74
    vg
    nfv
    @48
    vg
    vh
    @46
    vf
    vg
    @23
    @23
    nfra2
    nfal
    nf3an
    @63
    vg
    nfv
    nfan
    @75
    @63
    @64
    @55
    @75
    @65
    wa
    #
    @54
    @20
    @76
    @54
    wa
    #
    vy
    vz
    cA
    vf
    vg
    vh
    vi
    @10
    @12
    @15
    cI
    @41
    cN
    cX
    vs
    @75
    @68
    @65
    @54
    wph
    @74
    @68
    @49
    mreexexlem2d.1
    3ad2ant1
    ad2antrr
    mreexexlem2d.2
    mreexexlem2d.3
    @75
    @71
    @65
    @54
    wph
    @74
    @71
    @49
    mreexexlem2d.4
    3ad2ant1
    ad2antrr
    @77
    @10
    @22
    @75
    @63
    @64
    @54
    simplrl
    elpwid
    @77
    @12
    @22
    @75
    @63
    @64
    @54
    simplrr
    elpwid
    @76
    @53
    @16
    @17
    simpr2
    @76
    @53
    @16
    @17
    simpr3
    wph
    @74
    @49
    @65
    @54
    simpll2
    wph
    @74
    @49
    @65
    @54
    simpll3
    @76
    @53
    @16
    @17
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
