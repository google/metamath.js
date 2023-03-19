include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "w3a.mm"
include "wa.mm"
include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "co.mm"
include "wcel.mm"
include "cfn.mm"
include "isfinite.mm"
include "wi.mm"
include "ccrd.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "simpr.mm"
include "vex.mm"
include "pwfseqlem2.mm"
include "sylancl.mm"
include "wf.mm"
include "wf1o.mm"
include "f1of.mm"
include "syl.mm"
include "fssd.mm"
include "ficardom.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eqeltrd.mm"
include "ex.mm"
include "adantr.mm"
include "syl5bir.mm"
include "wn.mm"
include "cdom.mm"
include "cdm.mm"
include "wb.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "wex.mm"
include "simpr3.mm"
include "19.8a.mm"
include "ween.mm"
include "sylibr.mm"
include "domtri2.mm"
include "sylancr.mm"
include "cdif.mm"
include "nfv.mm"
include "nfcv.mm"
include "crab.mm"
include "cint.mm"
include "cif.mm"
include "cmpt2.mm"
include "nfmpt22.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfel1.mm"
include "nfim.mm"
include "weq.mm"
include "sseq1.mm"
include "weeq1.mm"
include "3anbi23d.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "nfmpt21.mm"
include "xpeq12.mm"
include "anidms.mm"
include "sseq2d.mm"
include "weeq2.mm"
include "3anbi123d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "oveq1.mm"
include "difeq2.mm"
include "eleq12d.mm"
include "pwfseqlem3.mm"
include "chvar.mm"
include "eldifad.mm"
include "expr.mm"
include "sylbird.mm"
include "pm2.61d.mm"

theorem pwfseqlem4a
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vy: setvar y
  let vb: setvar b
  let vv: setvar v
  let cR: class R
  let cW: class W
  let cZ: class Z
  let cY: class Y
  let cV: class V
  assume pwfseqlem4.g: |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) )
  assume pwfseqlem4.x: |- ( ph -> X C_ A )
  assume pwfseqlem4.h: |- ( ph -> H : _om -1-1-onto-> X )
  assume pwfseqlem4.ps: |- ( ps <-> ( ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) /\ _om ~<_ x ) )
  assume pwfseqlem4.k: |- ( ( ph /\ ps ) -> K : U_ n e. _om ( x ^m n ) -1-1-> x )
  assume pwfseqlem4.d: |- D = ( G ` { w e. x | ( ( `' K ` w ) e. ran G /\ -. w e. ( `' G ` ( `' K ` w ) ) ) } )
  assume pwfseqlem4.f: |- F = ( x e. _V , r e. _V |-> if ( x e. Fin , ( H ` ( card ` x ) ) , ( D ` |^| { z e. _om | -. ( D ` z ) e. x } ) ) )

  disjoint n r
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint r w
  disjoint r x
  disjoint r z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint D n
  disjoint D z
  disjoint a s
  disjoint F a
  disjoint F s
  disjoint G w
  disjoint K w
  disjoint a r
  disjoint a x
  disjoint a z
  disjoint H a
  disjoint r s
  disjoint H r
  disjoint s x
  disjoint s z
  disjoint H s
  disjoint H x
  disjoint H z
  disjoint a n
  disjoint a ph
  disjoint n s
  disjoint n ph
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph z
  disjoint n ps
  disjoint ps z
  disjoint A a
  disjoint A n
  disjoint A r
  disjoint A s
  disjoint A x
  disjoint A z
  disjoint n y
  disjoint y z
  disjoint D y
  disjoint a b
  disjoint a v
  disjoint a y
  disjoint b s
  disjoint b v
  disjoint b y
  disjoint F b
  disjoint s v
  disjoint s y
  disjoint v y
  disjoint F v
  disjoint F y
  disjoint w y
  disjoint G y
  disjoint K y
  disjoint b r
  disjoint b x
  disjoint b z
  disjoint H b
  disjoint r v
  disjoint r y
  disjoint v x
  disjoint v z
  disjoint H v
  disjoint x y
  disjoint H y
  disjoint b n
  disjoint b ph
  disjoint n v
  disjoint ph v
  disjoint R s
  disjoint A y
  disjoint W a
  disjoint W b
  disjoint W s
  disjoint W v
  disjoint Z a
  disjoint Z b
  disjoint Z s
  disjoint Z v
  disjoint Y a
  disjoint Y s
  disjoint V a
  disjoint V r
  disjoint V s
  disjoint V x
  assert |- ( ( ph /\ ( a C_ A /\ s C_ ( a X. a ) /\ s We a ) ) -> ( a F s ) e. A )

  proof
    wph
    va
    cv
    #
    cA
    wss
    #
    vs
    cv
    #
    @0
    @0
    cxp
    #
    wss
    #
    @0
    @2
    wwe
    #
    w3a
    #
    wa
    #
    @0
    com
    csdm
    wbr
    #
    @0
    @2
    cF
    co
    #
    cA
    wcel
    #
    @8
    @0
    cfn
    wcel
    #
    @7
    @10
    @0
    isfinite
    wph
    @11
    @10
    wi
    @6
    wph
    @11
    @10
    wph
    @11
    wa
    #
    @9
    @0
    ccrd
    cfv
    #
    cH
    cfv
    #
    cA
    @12
    @11
    @2
    cvv
    wcel
    @9
    @14
    wceq
    wph
    @11
    simpr
    vs
    vex
    wph
    wps
    vx
    vz
    vw
    cA
    cD
    @2
    vn
    cF
    cG
    cH
    cK
    cvv
    cX
    @0
    vr
    pwfseqlem4.g
    pwfseqlem4.x
    pwfseqlem4.h
    pwfseqlem4.ps
    pwfseqlem4.k
    pwfseqlem4.d
    pwfseqlem4.f
    pwfseqlem2
    sylancl
    wph
    com
    cA
    cH
    wf
    @13
    com
    wcel
    @14
    cA
    wcel
    @11
    wph
    com
    cX
    cA
    cH
    wph
    com
    cX
    cH
    wf1o
    com
    cX
    cH
    wf
    pwfseqlem4.h
    com
    cX
    cH
    f1of
    syl
    pwfseqlem4.x
    fssd
    @0
    ficardom
    com
    cA
    @13
    cH
    ffvelrn
    syl2an
    eqeltrd
    ex
    adantr
    syl5bir
    @7
    @8
    wn
    #
    com
    @0
    cdom
    wbr
    #
    @10
    @7
    com
    ccrd
    cdm
    #
    wcel
    #
    @0
    @17
    wcel
    #
    @16
    @15
    wb
    com
    con0
    wcel
    @18
    omelon
    com
    onenon
    ax-mp
    @7
    @5
    vs
    wex
    #
    @19
    @7
    @5
    @20
    wph
    @1
    @4
    @5
    simpr3
    @5
    vs
    19.8a
    syl
    @0
    vs
    ween
    sylibr
    com
    @0
    domtri2
    sylancr
    wph
    @6
    @16
    @10
    wph
    @6
    @16
    wa
    #
    wa
    #
    @9
    cA
    @0
    wph
    @1
    vr
    cv
    #
    @3
    wss
    #
    @0
    @23
    wwe
    #
    w3a
    #
    @16
    wa
    #
    wa
    #
    @0
    @23
    cF
    co
    #
    cA
    @0
    cdif
    #
    wcel
    #
    wi
    #
    @22
    @9
    @30
    wcel
    #
    wi
    vr
    vs
    @22
    @33
    vr
    @22
    vr
    nfv
    vr
    @9
    @30
    vr
    @0
    @2
    cF
    vr
    @0
    nfcv
    vr
    cF
    vx
    vr
    cvv
    cvv
    vx
    cv
    #
    cfn
    wcel
    @34
    ccrd
    cfv
    cH
    cfv
    vz
    cv
    cD
    cfv
    @34
    wcel
    wn
    vz
    com
    crab
    cint
    cD
    cfv
    cif
    #
    cmpt2
    #
    pwfseqlem4.f
    vx
    vr
    cvv
    cvv
    @35
    nfmpt22
    nfcxfr
    vr
    @2
    nfcv
    nfov
    nfel1
    nfim
    vr
    vs
    weq
    #
    @28
    @22
    @31
    @33
    @37
    @27
    @21
    wph
    @37
    @26
    @6
    @16
    @37
    @24
    @4
    @25
    @5
    @1
    @23
    @2
    @3
    sseq1
    @0
    @23
    @2
    weeq1
    3anbi23d
    anbi1d
    anbi2d
    @37
    @29
    @9
    @30
    @23
    @2
    @0
    cF
    oveq2
    eleq1d
    imbi12d
    wph
    wps
    wa
    #
    @34
    @23
    cF
    co
    #
    cA
    @34
    cdif
    #
    wcel
    #
    wi
    @32
    vx
    va
    @28
    @31
    vx
    @28
    vx
    nfv
    vx
    @29
    @30
    vx
    @0
    @23
    cF
    vx
    @0
    nfcv
    vx
    cF
    @36
    pwfseqlem4.f
    vx
    vr
    cvv
    cvv
    @35
    nfmpt21
    nfcxfr
    vx
    @23
    nfcv
    nfov
    nfel1
    nfim
    vx
    va
    weq
    #
    @38
    @28
    @41
    @31
    @42
    wps
    @27
    wph
    wps
    @34
    cA
    wss
    #
    @23
    @34
    @34
    cxp
    #
    wss
    #
    @34
    @23
    wwe
    #
    w3a
    #
    com
    @34
    cdom
    wbr
    #
    wa
    @42
    @27
    pwfseqlem4.ps
    @42
    @47
    @26
    @48
    @16
    @42
    @43
    @1
    @45
    @24
    @46
    @25
    @34
    @0
    cA
    sseq1
    @42
    @44
    @3
    @23
    @42
    @44
    @3
    wceq
    @34
    @0
    @34
    @0
    xpeq12
    anidms
    sseq2d
    @34
    @0
    @23
    weeq2
    3anbi123d
    @34
    @0
    com
    cdom
    breq2
    anbi12d
    syl5bb
    anbi2d
    @42
    @39
    @29
    @40
    @30
    @34
    @0
    @23
    cF
    oveq1
    @34
    @0
    cA
    difeq2
    eleq12d
    imbi12d
    wph
    wps
    vx
    vz
    vw
    cA
    cD
    vn
    cF
    cG
    cH
    cK
    cX
    vr
    pwfseqlem4.g
    pwfseqlem4.x
    pwfseqlem4.h
    pwfseqlem4.ps
    pwfseqlem4.k
    pwfseqlem4.d
    pwfseqlem4.f
    pwfseqlem3
    chvar
    chvar
    eldifad
    expr
    sylbird
    pm2.61d
end
