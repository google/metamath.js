include "wcel.mm"
include "cfin3.mm"
include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "wss.mm"
include "com.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "elmapi.mm"
include "isf34lem7.mm"
include "3expia.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "cint.mm"
include "ccom.mm"
include "cima.mm"
include "cvv.mm"
include "elmapex.mm"
include "simpld.mm"
include "pwexb.mm"
include "sylibr.mm"
include "isf34lem2.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "wa.mm"
include "wb.mm"
include "elmapg.mm"
include "mpbird.mm"
include "wceq.mm"
include "fveq1.mm"
include "sseq12d.mm"
include "ralbidv.mm"
include "rneq.mm"
include "rnco2.mm"
include "syl6eq.mm"
include "unieqd.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl5.mm"
include "cdif.mm"
include "sscon.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "isf34lem1.mm"
include "peano2.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "syl5ibr.mm"
include "fvco3.mm"
include "sylan.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "wfn.mm"
include "ffn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "fnfvima.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "cin.mm"
include "incom.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "peano1.mm"
include "ne0i.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "imadisj.mm"
include "isf34lem4.mm"
include "syl12anc.mm"
include "isf34lem3.mm"
include "inteqd.mm"
include "eqtrd.mm"
include "sylibd.mm"
include "imim12d.mm"
include "sylcom.mm"
include "ralrimiv.mm"
include "isfin3-3.mm"
include "impbid2.mm"

theorem isf34lem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  let cX: class X
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint F a
  disjoint F b
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( A e. V -> ( A e. Fin3 <-> A. f e. ( ~P A ^m _om ) ( A. y e. _om ( f ` y ) C_ ( f ` suc y ) -> U. ran f e. ran f ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfin3
    wcel
    #
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    @2
    csuc
    #
    @3
    cfv
    #
    wss
    #
    vy
    com
    wral
    #
    @3
    crn
    #
    cuni
    #
    @9
    wcel
    #
    wi
    #
    vf
    cA
    cpw
    #
    com
    cmap
    co
    #
    wral
    #
    @1
    @12
    vf
    @14
    @3
    @14
    wcel
    @1
    com
    @13
    @3
    wf
    #
    @12
    @3
    @13
    com
    elmapi
    @1
    @16
    @8
    @11
    vx
    vy
    cA
    cF
    @3
    compss.a
    isf34lem7
    3expia
    sylan2
    ralrimiva
    @15
    @1
    @0
    @5
    vg
    cv
    #
    cfv
    #
    @2
    @17
    cfv
    #
    wss
    #
    vy
    com
    wral
    #
    @17
    crn
    #
    cint
    #
    @22
    wcel
    #
    wi
    #
    vg
    @14
    wral
    @15
    @25
    vg
    @14
    @15
    @17
    @14
    wcel
    #
    @2
    cF
    @17
    ccom
    #
    cfv
    #
    @5
    @27
    cfv
    #
    wss
    #
    vy
    com
    wral
    #
    cF
    @22
    cima
    #
    cuni
    #
    @32
    wcel
    #
    wi
    #
    @25
    @26
    @27
    @14
    wcel
    #
    @15
    @35
    @26
    @36
    com
    @13
    @27
    wf
    #
    @26
    @13
    @13
    cF
    wf
    #
    com
    @13
    @17
    wf
    #
    @37
    @26
    cA
    cvv
    wcel
    #
    @38
    @26
    @13
    cvv
    wcel
    #
    @40
    @26
    @41
    com
    cvv
    wcel
    #
    @17
    @13
    com
    elmapex
    #
    simpld
    cA
    pwexb
    sylibr
    #
    vx
    cA
    cF
    cvv
    compss.a
    isf34lem2
    syl
    #
    @17
    @13
    com
    elmapi
    #
    com
    @13
    @13
    cF
    @17
    fco
    syl2anc
    @26
    @41
    @42
    wa
    @36
    @37
    wb
    @43
    @13
    com
    @27
    cvv
    cvv
    elmapg
    syl
    mpbird
    @12
    @35
    vf
    @27
    @14
    @3
    @27
    wceq
    #
    @8
    @31
    @11
    @34
    @47
    @7
    @30
    vy
    com
    @47
    @4
    @28
    @6
    @29
    @2
    @3
    @27
    fveq1
    @5
    @3
    @27
    fveq1
    sseq12d
    ralbidv
    @47
    @10
    @33
    @9
    @32
    @47
    @9
    @32
    @47
    @9
    @27
    crn
    @32
    @3
    @27
    rneq
    cF
    @17
    rnco2
    syl6eq
    #
    unieqd
    @48
    eleq12d
    imbi12d
    rspccv
    syl5
    @26
    @21
    @31
    @34
    @24
    @26
    @20
    @30
    vy
    com
    @26
    @2
    com
    wcel
    #
    wa
    #
    @20
    @19
    cF
    cfv
    #
    @18
    cF
    cfv
    #
    wss
    #
    @30
    @20
    @53
    @50
    cA
    @19
    cdif
    #
    cA
    @18
    cdif
    #
    wss
    @18
    @19
    cA
    sscon
    @50
    @51
    @54
    @52
    @55
    @50
    @40
    @19
    cA
    wss
    @51
    @54
    wceq
    @26
    @40
    @49
    @44
    adantr
    #
    @50
    @19
    cA
    @26
    com
    @13
    @2
    @17
    @46
    ffvelrnda
    elpwid
    vx
    cA
    cF
    cvv
    @19
    compss.a
    isf34lem1
    syl2anc
    @50
    @40
    @18
    cA
    wss
    @52
    @55
    wceq
    @56
    @50
    @18
    cA
    @26
    @39
    @5
    com
    wcel
    #
    @18
    @13
    wcel
    @49
    @46
    @2
    peano2
    #
    com
    @13
    @5
    @17
    ffvelrn
    syl2an
    elpwid
    vx
    cA
    cF
    cvv
    @18
    compss.a
    isf34lem1
    syl2anc
    sseq12d
    syl5ibr
    @50
    @28
    @51
    @29
    @52
    @26
    @39
    @49
    @28
    @51
    wceq
    @46
    com
    @13
    @2
    cF
    @17
    fvco3
    sylan
    @26
    @39
    @57
    @29
    @52
    wceq
    @49
    @46
    @58
    com
    @13
    @5
    cF
    @17
    fvco3
    syl2an
    sseq12d
    sylibrd
    ralimdva
    @26
    @34
    @33
    cF
    cfv
    #
    cF
    @32
    cima
    #
    wcel
    #
    @24
    @26
    cF
    @13
    wfn
    #
    @32
    @13
    wss
    #
    @34
    @61
    wi
    @26
    @38
    @62
    @45
    @13
    @13
    cF
    ffn
    syl
    @26
    @32
    cF
    crn
    #
    @13
    cF
    @22
    imassrn
    @26
    @38
    @64
    @13
    wss
    @45
    @13
    @13
    cF
    frn
    syl
    syl5ss
    #
    @62
    @63
    @34
    @61
    @13
    @32
    cF
    @33
    fnfvima
    3expia
    syl2anc
    @26
    @59
    @23
    @60
    @22
    @26
    @59
    @60
    cint
    #
    @23
    @26
    @40
    @63
    @32
    c0
    wne
    #
    @59
    @66
    wceq
    @44
    @65
    @26
    cF
    cdm
    #
    @22
    cin
    #
    c0
    wne
    @67
    @26
    @69
    @22
    c0
    @26
    @69
    @22
    @68
    cin
    #
    @22
    @68
    @22
    incom
    @26
    @22
    @68
    wss
    @70
    @22
    wceq
    @26
    @22
    @13
    @68
    @26
    @39
    @22
    @13
    wss
    #
    @46
    com
    @13
    @17
    frn
    syl
    #
    @26
    @38
    @68
    @13
    wceq
    @45
    @13
    @13
    cF
    fdm
    syl
    sseqtr4d
    @22
    @68
    df-ss
    sylib
    syl5eq
    @26
    @17
    cdm
    #
    c0
    wne
    @22
    c0
    wne
    @26
    @73
    com
    c0
    @26
    @39
    @73
    com
    wceq
    @46
    com
    @13
    @17
    fdm
    syl
    c0
    com
    wcel
    com
    c0
    wne
    @26
    peano1
    com
    c0
    ne0i
    mp1i
    eqnetrd
    @73
    c0
    @22
    c0
    @17
    dm0rn0
    necon3bii
    sylib
    eqnetrd
    @32
    c0
    @69
    c0
    cF
    @22
    imadisj
    necon3bii
    sylibr
    vx
    cA
    cF
    cvv
    @32
    compss.a
    isf34lem4
    syl12anc
    @26
    @60
    @22
    @26
    @40
    @71
    @60
    @22
    wceq
    @44
    @72
    vx
    cA
    cF
    cvv
    @22
    compss.a
    isf34lem3
    syl2anc
    #
    inteqd
    eqtrd
    @74
    eleq12d
    sylibd
    imim12d
    sylcom
    ralrimiv
    vy
    cA
    vg
    cV
    isfin3-3
    syl5ibr
    impbid2
end
