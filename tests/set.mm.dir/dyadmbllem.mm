include "cicc.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "eluni2.mm"
include "cfv.mm"
include "cxr.mm"
include "cxp.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "cpw.mm"
include "wf.mm"
include "iccf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "crn.mm"
include "cle.mm"
include "cr.mm"
include "cin.mm"
include "cz.mm"
include "cn0.mm"
include "dyadf.mm"
include "frn.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "syl6ss.mm"
include "eleq2.mm"
include "rexima.mm"
include "sylancr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "crab.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "adantr.mm"
include "syl5ss.mm"
include "simprl.mm"
include "ssid.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "rabn0.mm"
include "sylibr.mm"
include "dyadmax.mm"
include "syl2anc.mm"
include "elrab.mm"
include "simprlr.mm"
include "simplrr.mm"
include "sseldd.mm"
include "simprll.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "sstr2.mm"
include "ad2antll.mm"
include "ancrd.mm"
include "imim1d.mm"
include "syl5bir.mm"
include "imim2d.mm"
include "syl5bi.mm"
include "ralimdv2.mm"
include "impr.mm"
include "sseq1d.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "eqsstri.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "ad2antrr.mm"
include "funfvima2.mm"
include "mpd.mm"
include "elunii.mm"
include "exp32.mm"
include "rexlimdv.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "imass2.mm"
include "uniss.mm"
include "mp1i.mm"
include "eqssd.mm"

theorem dyadmbllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )
  assume dyadmbl.2: |- G = { z e. A | A. w e. A ( ( [,] ` z ) C_ ( [,] ` w ) -> z = w ) }
  assume dyadmbl.3: |- ( ph -> A C_ ran F )

  disjoint x y
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  assert |- ( ph -> U. ( [,] " A ) = U. ( [,] " G ) )

  proof
    wph
    cicc
    cA
    cima
    #
    cuni
    #
    cicc
    cG
    cima
    #
    cuni
    #
    wph
    va
    @1
    @3
    va
    cv
    #
    @1
    wcel
    @4
    vi
    cv
    #
    wcel
    #
    vi
    @0
    wrex
    #
    wph
    @4
    @3
    wcel
    #
    vi
    @4
    @0
    eluni2
    wph
    @7
    @4
    vt
    cv
    #
    cicc
    cfv
    #
    wcel
    #
    vt
    cA
    wrex
    #
    @8
    wph
    cicc
    cxr
    cxr
    cxp
    #
    wfn
    #
    cA
    @13
    wss
    @7
    @12
    wb
    @13
    cxr
    cpw
    #
    cicc
    wf
    #
    @14
    iccf
    @13
    @15
    cicc
    ffn
    ax-mp
    wph
    cA
    cF
    crn
    #
    @13
    dyadmbl.3
    @17
    cle
    cr
    cr
    cxp
    #
    cin
    #
    @13
    cz
    cn0
    cxp
    #
    @19
    cF
    wf
    @17
    @19
    wss
    vx
    vy
    cF
    dyadmbl.1
    dyadf
    @20
    @19
    cF
    frn
    ax-mp
    @19
    @18
    @13
    cle
    @18
    inss2
    rexpssxrxp
    sstri
    sstri
    syl6ss
    #
    @6
    @11
    vi
    vt
    @13
    cA
    cicc
    @5
    @10
    @4
    eleq2
    rexima
    sylancr
    wph
    @11
    @8
    vt
    cA
    wph
    @9
    cA
    wcel
    #
    @11
    wa
    #
    wa
    #
    vm
    cv
    #
    cicc
    cfv
    #
    vw
    cv
    #
    cicc
    cfv
    #
    wss
    #
    vm
    vw
    weq
    #
    wi
    #
    vw
    @10
    @4
    cicc
    cfv
    #
    wss
    #
    va
    cA
    crab
    #
    wral
    #
    vm
    @34
    wrex
    #
    @8
    @24
    @34
    @17
    wss
    @34
    c0
    wne
    #
    @36
    @24
    @34
    cA
    @17
    @33
    va
    cA
    ssrab2
    wph
    cA
    @17
    wss
    @23
    dyadmbl.3
    adantr
    syl5ss
    @24
    @33
    va
    cA
    wrex
    #
    @37
    @24
    @22
    @10
    @10
    wss
    #
    @38
    wph
    @22
    @11
    simprl
    @10
    ssid
    @33
    @39
    va
    @9
    cA
    va
    vt
    weq
    @32
    @10
    @10
    @4
    @9
    cicc
    fveq2
    sseq2d
    rspcev
    sylancl
    @33
    va
    cA
    rabn0
    sylibr
    vx
    vy
    vm
    vw
    @34
    cF
    dyadmbl.1
    dyadmax
    syl2anc
    @24
    @35
    @8
    vm
    @34
    @25
    @34
    wcel
    @25
    cA
    wcel
    #
    @10
    @26
    wss
    #
    wa
    #
    @24
    @35
    @8
    wi
    @33
    @41
    va
    @25
    cA
    va
    vm
    weq
    @32
    @26
    @10
    @4
    @25
    cicc
    fveq2
    sseq2d
    elrab
    @24
    @42
    @35
    @8
    @24
    @42
    @35
    wa
    #
    wa
    #
    @4
    @26
    wcel
    @26
    @2
    wcel
    #
    @8
    @44
    @10
    @26
    @4
    @24
    @40
    @41
    @35
    simprlr
    wph
    @22
    @11
    @43
    simplrr
    sseldd
    @44
    @25
    cG
    wcel
    #
    @45
    @44
    @40
    @31
    vw
    cA
    wral
    #
    @46
    @24
    @40
    @41
    @35
    simprll
    @24
    @42
    @35
    @47
    @24
    @42
    wa
    #
    @31
    @31
    vw
    @34
    cA
    @27
    @34
    wcel
    #
    @31
    wi
    #
    @27
    cA
    wcel
    #
    @10
    @28
    wss
    #
    @31
    wi
    #
    wi
    #
    @48
    @51
    @31
    wi
    @50
    @51
    @52
    wa
    #
    @31
    wi
    @54
    @49
    @55
    @31
    @33
    @52
    va
    @27
    cA
    va
    vw
    weq
    @32
    @28
    @10
    @4
    @27
    cicc
    fveq2
    sseq2d
    elrab
    imbi1i
    @51
    @52
    @31
    impexp
    bitri
    @48
    @53
    @31
    @51
    @53
    @52
    @29
    wa
    #
    @30
    wi
    @48
    @31
    @52
    @29
    @30
    impexp
    @48
    @29
    @56
    @30
    @48
    @29
    @52
    @41
    @29
    @52
    wi
    @24
    @40
    @10
    @26
    @28
    sstr2
    ad2antll
    ancrd
    imim1d
    syl5bir
    imim2d
    syl5bi
    ralimdv2
    impr
    vz
    cv
    #
    cicc
    cfv
    #
    @28
    wss
    #
    vz
    vw
    weq
    #
    wi
    #
    vw
    cA
    wral
    #
    @47
    vz
    @25
    cA
    cG
    vz
    vm
    weq
    #
    @61
    @31
    vw
    cA
    @63
    @59
    @29
    @60
    @30
    @63
    @58
    @26
    @28
    @57
    @25
    cicc
    fveq2
    sseq1d
    vz
    vm
    vw
    equequ1
    imbi12d
    ralbidv
    dyadmbl.2
    elrab2
    sylanbrc
    @44
    cicc
    wfun
    #
    cG
    cicc
    cdm
    #
    wss
    #
    @46
    @45
    wi
    @16
    @64
    iccf
    @13
    @15
    cicc
    ffun
    ax-mp
    wph
    @66
    @23
    @43
    wph
    cG
    @13
    @65
    wph
    cG
    cA
    @13
    cG
    @62
    vz
    cA
    crab
    cA
    dyadmbl.2
    @62
    vz
    cA
    ssrab2
    eqsstri
    #
    @21
    syl5ss
    @13
    @15
    cicc
    iccf
    fdmi
    syl6sseqr
    ad2antrr
    cG
    @25
    cicc
    funfvima2
    sylancr
    mpd
    @4
    @26
    @2
    elunii
    syl2anc
    exp32
    syl5bi
    rexlimdv
    mpd
    rexlimdvaa
    sylbid
    syl5bi
    ssrdv
    @2
    @0
    wss
    #
    @3
    @1
    wss
    wph
    cG
    cA
    wss
    @68
    @67
    cG
    cA
    cicc
    imass2
    ax-mp
    @2
    @0
    uniss
    mp1i
    eqssd
end
