include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "com.mm"
include "crab.mm"
include "cint.mm"
include "cdif.mm"
include "cfn.mm"
include "ccrd.mm"
include "cif.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "fvex.mm"
include "ifex.mm"
include "ovmpt4g.mm"
include "mp3an.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "w3a.mm"
include "simprbi.mm"
include "adantl.mm"
include "domnsym.mm"
include "syl.mm"
include "isfinite.mm"
include "sylnibr.mm"
include "iffalsed.mm"
include "syl5eq.mm"
include "cmap.mm"
include "ciun.mm"
include "wrex.mm"
include "pwfseqlem1.mm"
include "eldif.mm"
include "sylib.mm"
include "simpld.mm"
include "eliun.mm"
include "wf.mm"
include "elmapi.mm"
include "ad2antll.mm"
include "wral.mm"
include "ssiun2.mm"
include "ad2antrl.mm"
include "simprd.mm"
include "adantr.mm"
include "ssneldd.mm"
include "elmap.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "ffnfv.mm"
include "baib.mm"
include "3syl.mm"
include "syl5bb.mm"
include "mtbid.mm"
include "con0.mm"
include "nnon.mm"
include "ssrab2.mm"
include "omsson.mm"
include "sstri.mm"
include "c0.mm"
include "wne.mm"
include "word.mm"
include "ordom.mm"
include "simprl.mm"
include "ordelss.mm"
include "sylancr.mm"
include "rexnal.mm"
include "sylibr.mm"
include "ssrexv.mm"
include "sylc.mm"
include "rabn0.mm"
include "onint.mm"
include "sseldi.mm"
include "ontri1.mm"
include "syl2anc.mm"
include "wi.mm"
include "ssintrab.mm"
include "syl2an.mm"
include "imbi2d.mm"
include "con34b.mm"
include "syl6bbr.mm"
include "pm5.74da.mm"
include "bi2.04.mm"
include "syl6bb.mm"
include "elnn.mm"
include "pm2.27.mm"
include "expcom.mm"
include "a2d.mm"
include "sylbid.mm"
include "ralimdv2.mm"
include "syl5bi.mm"
include "sylbird.mm"
include "mt3d.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "notbid.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "eldifd.mm"
include "rexlimddv.mm"
include "eqeltrd.mm"

theorem pwfseqlem3
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
  let vr: setvar r
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
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
  disjoint G w
  disjoint K w
  disjoint H r
  disjoint H x
  disjoint H z
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint n ps
  disjoint ps z
  disjoint A n
  disjoint A r
  disjoint A x
  disjoint A z
  disjoint n y
  disjoint y z
  disjoint D y
  disjoint a b
  disjoint a s
  disjoint a v
  disjoint a y
  disjoint F a
  disjoint b s
  disjoint b v
  disjoint b y
  disjoint F b
  disjoint s v
  disjoint s y
  disjoint F s
  disjoint v y
  disjoint F v
  disjoint F y
  disjoint w y
  disjoint G y
  disjoint K y
  disjoint a r
  disjoint a x
  disjoint a z
  disjoint H a
  disjoint b r
  disjoint b x
  disjoint b z
  disjoint H b
  disjoint r s
  disjoint r v
  disjoint r y
  disjoint s x
  disjoint s z
  disjoint H s
  disjoint v x
  disjoint v z
  disjoint H v
  disjoint x y
  disjoint H y
  disjoint a n
  disjoint a ph
  disjoint b n
  disjoint b ph
  disjoint n s
  disjoint n v
  disjoint ph s
  disjoint ph v
  disjoint R s
  disjoint A a
  disjoint A s
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
  assert |- ( ( ph /\ ps ) -> ( x F r ) e. ( A \ x ) )

  proof
    wph
    wps
    wa
    #
    vx
    cv
    #
    vr
    cv
    #
    cF
    co
    #
    vz
    cv
    #
    cD
    cfv
    #
    @1
    wcel
    #
    wn
    #
    vz
    com
    crab
    #
    cint
    #
    cD
    cfv
    #
    cA
    @1
    cdif
    #
    @0
    @3
    @1
    cfn
    wcel
    #
    @1
    ccrd
    cfv
    #
    cH
    cfv
    #
    @10
    cif
    #
    @10
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @15
    cvv
    wcel
    @3
    @15
    wceq
    vx
    vex
    #
    vr
    vex
    @12
    @14
    @10
    @13
    cH
    fvex
    @9
    cD
    fvex
    ifex
    vx
    vr
    cvv
    cvv
    @15
    cF
    cvv
    pwfseqlem4.f
    ovmpt4g
    mp3an
    @0
    @12
    @14
    @10
    @0
    @1
    com
    csdm
    wbr
    #
    @12
    @0
    com
    @1
    cdom
    wbr
    #
    @17
    wn
    wps
    @18
    wph
    wps
    @1
    cA
    wss
    @2
    @1
    @1
    cxp
    wss
    @1
    @2
    wwe
    w3a
    @18
    pwfseqlem4.ps
    simprbi
    adantl
    com
    @1
    domnsym
    syl
    @1
    isfinite
    sylnibr
    iffalsed
    syl5eq
    @0
    cD
    cA
    vn
    cv
    #
    cmap
    co
    #
    wcel
    #
    @10
    @11
    wcel
    vn
    com
    @0
    cD
    vn
    com
    @20
    ciun
    #
    wcel
    #
    @21
    vn
    com
    wrex
    @0
    @23
    cD
    vn
    com
    @1
    @19
    cmap
    co
    #
    ciun
    #
    wcel
    wn
    #
    @0
    cD
    @22
    @25
    cdif
    wcel
    @23
    @26
    wa
    wph
    wps
    vx
    vw
    cA
    cD
    vn
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
    pwfseqlem1
    cD
    @22
    @25
    eldif
    sylib
    #
    simpld
    vn
    cD
    com
    @20
    eliun
    sylib
    @0
    @19
    com
    wcel
    #
    @21
    wa
    #
    wa
    #
    @10
    cA
    @1
    @30
    @19
    cA
    @9
    cD
    @21
    @19
    cA
    cD
    wf
    #
    @0
    @28
    cD
    cA
    @19
    elmapi
    ad2antll
    #
    @30
    @9
    @19
    wcel
    #
    @6
    vz
    @19
    wral
    #
    @30
    cD
    @24
    wcel
    #
    @34
    @30
    @24
    @25
    cD
    @28
    @24
    @25
    wss
    @0
    @21
    vn
    com
    @24
    ssiun2
    ad2antrl
    @0
    @26
    @29
    @0
    @23
    @26
    @27
    simprd
    adantr
    ssneldd
    @35
    @19
    @1
    cD
    wf
    #
    @30
    @34
    @1
    @19
    cD
    @16
    vn
    vex
    elmap
    @30
    @31
    cD
    @19
    wfn
    #
    @36
    @34
    wb
    @32
    @19
    cA
    cD
    ffn
    @36
    @37
    @34
    vz
    @19
    @1
    cD
    ffnfv
    baib
    3syl
    syl5bb
    mtbid
    #
    @30
    @33
    wn
    #
    @19
    @9
    wss
    #
    @34
    @30
    @19
    con0
    wcel
    #
    @9
    con0
    wcel
    @40
    @39
    wb
    @28
    @41
    @0
    @21
    @19
    nnon
    #
    ad2antrl
    @30
    @8
    con0
    @9
    @8
    com
    con0
    @7
    vz
    com
    ssrab2
    omsson
    sstri
    #
    @30
    @8
    con0
    wss
    @8
    c0
    wne
    #
    @9
    @8
    wcel
    #
    @43
    @30
    @7
    vz
    com
    wrex
    #
    @44
    @30
    @19
    com
    wss
    #
    @7
    vz
    @19
    wrex
    #
    @46
    @30
    com
    word
    @28
    @47
    ordom
    @0
    @28
    @21
    simprl
    com
    @19
    ordelss
    sylancr
    @30
    @34
    wn
    @48
    @38
    @6
    vz
    @19
    rexnal
    sylibr
    @7
    vz
    @19
    com
    ssrexv
    sylc
    @7
    vz
    com
    rabn0
    sylibr
    @8
    onint
    sylancr
    #
    sseldi
    @19
    @9
    ontri1
    syl2anc
    @40
    @7
    @19
    @4
    wss
    #
    wi
    #
    vz
    com
    wral
    @30
    @34
    @7
    vz
    @19
    com
    ssintrab
    @30
    @51
    @6
    vz
    com
    @19
    @28
    @4
    com
    wcel
    #
    @51
    wi
    #
    @4
    @19
    wcel
    #
    @6
    wi
    #
    wi
    @0
    @21
    @28
    @53
    @54
    @52
    @6
    wi
    #
    wi
    #
    @55
    @28
    @53
    @52
    @55
    wi
    @57
    @28
    @52
    @51
    @55
    @28
    @52
    wa
    #
    @51
    @7
    @54
    wn
    #
    wi
    @55
    @58
    @50
    @59
    @7
    @28
    @41
    @4
    con0
    wcel
    @50
    @59
    wb
    @52
    @42
    @4
    nnon
    @19
    @4
    ontri1
    syl2an
    imbi2d
    @54
    @6
    con34b
    syl6bbr
    pm5.74da
    @52
    @54
    @6
    bi2.04
    syl6bb
    @28
    @54
    @56
    @6
    @54
    @28
    @56
    @6
    wi
    #
    @54
    @28
    wa
    @52
    @60
    @4
    @19
    elnn
    @52
    @6
    pm2.27
    syl
    expcom
    a2d
    sylbid
    ad2antrl
    ralimdv2
    syl5bi
    sylbird
    mt3d
    ffvelrnd
    @30
    @45
    @10
    @1
    wcel
    #
    wn
    #
    @49
    @45
    @9
    com
    wcel
    @62
    vy
    cv
    #
    cD
    cfv
    #
    @1
    wcel
    #
    wn
    #
    @62
    vy
    @9
    com
    @8
    @63
    @9
    wceq
    #
    @65
    @61
    @67
    @64
    @10
    @1
    @63
    @9
    cD
    fveq2
    eleq1d
    notbid
    @7
    @66
    vz
    vy
    com
    @4
    @63
    wceq
    #
    @6
    @65
    @68
    @5
    @64
    @1
    @4
    @63
    cD
    fveq2
    eleq1d
    notbid
    cbvrabv
    elrab2
    simprbi
    syl
    eldifd
    rexlimddv
    eqeltrd
end
