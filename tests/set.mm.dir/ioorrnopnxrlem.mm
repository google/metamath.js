include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "wcel.mm"
include "cv.mm"
include "cioo.mm"
include "co.mm"
include "cixp.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "a1i.mm"
include "cmnf.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "cr.mm"
include "iftrue.mm"
include "adantl.mm"
include "adantr.mm"
include "simpr.mm"
include "fvixp2.mm"
include "syl2anc.mm"
include "elioored.mm"
include "1red.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "wne.mm"
include "neqne.mm"
include "cxr.mm"
include "ffvelrnda.mm"
include "cpnf.mm"
include "pnfxr.mm"
include "rexrd.mm"
include "clt.mm"
include "wbr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltpnfd.mm"
include "xrlttrd.mm"
include "xrltned.mm"
include "xrred.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "fmptd.mm"
include "caddc.mm"
include "readdcld.mm"
include "mnfxr.mm"
include "mnfltd.mm"
include "iooltub.mm"
include "xrgtned.mm"
include "ioorrnopn.mm"
include "cvv.mm"
include "wfn.mm"
include "wral.mm"
include "w3a.mm"
include "elexd.mm"
include "ixpfn.mm"
include "syl.mm"
include "cmpt.mm"
include "fvmpt2d.mm"
include "eqtrd.mm"
include "ltm1d.mm"
include "eqbrtrd.mm"
include "ltp1d.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "eliood.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "elixp2.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "cle.mm"
include "breq12d.mm"
include "mpbird.mm"
include "xrltled.mm"
include "eqled.mm"
include "ioossioo.mm"
include "syl22anc.mm"
include "ss2ixp.mm"
include "eqsstrd.mm"
include "jca.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem ioorrnopnxrlem
  let wph: wff ph
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let cF: class F
  let cL: class L
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ioorrnopnxrlem.x: |- ( ph -> X e. Fin )
  assume ioorrnopnxrlem.a: |- ( ph -> A : X --> RR* )
  assume ioorrnopnxrlem.b: |- ( ph -> B : X --> RR* )
  assume ioorrnopnxrlem.f: |- ( ph -> F e. X_ i e. X ( ( A ` i ) (,) ( B ` i ) ) )
  assume ioorrnopnxrlem.l: |- L = ( i e. X |-> if ( ( A ` i ) = -oo , ( ( F ` i ) - 1 ) , ( A ` i ) ) )
  assume ioorrnopnxrlem.r: |- R = ( i e. X |-> if ( ( B ` i ) = +oo , ( ( F ` i ) + 1 ) , ( B ` i ) ) )
  assume ioorrnopnxrlem.v: |- V = X_ i e. X ( ( L ` i ) (,) ( R ` i ) )

  disjoint A v
  disjoint B v
  disjoint F i
  disjoint F v
  disjoint i v
  disjoint L i
  disjoint R i
  disjoint V v
  disjoint X i
  disjoint X v
  disjoint i ph
  disjoint k x
  assert |- ( ph -> E. v e. ( TopOpen ` ( RR^ ` X ) ) ( F e. v /\ v C_ X_ i e. X ( ( A ` i ) (,) ( B ` i ) ) ) )

  proof
    wph
    cV
    cX
    crrx
    cfv
    ctopn
    cfv
    #
    wcel
    cF
    cV
    wcel
    #
    cV
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    cioo
    co
    #
    cixp
    #
    wss
    #
    wa
    #
    cF
    vv
    cv
    #
    wcel
    #
    @9
    @6
    wss
    #
    wa
    #
    vv
    @0
    wrex
    wph
    cV
    vi
    cX
    @2
    cL
    cfv
    #
    @2
    cR
    cfv
    #
    cioo
    co
    #
    cixp
    #
    @0
    cV
    @16
    wceq
    wph
    ioorrnopnxrlem.v
    a1i
    #
    wph
    cL
    cR
    vi
    cX
    ioorrnopnxrlem.x
    wph
    vi
    cX
    @3
    cmnf
    wceq
    #
    @2
    cF
    cfv
    #
    c1
    cmin
    co
    #
    @3
    cif
    #
    cr
    cL
    wph
    @2
    cX
    wcel
    #
    wa
    #
    @18
    @21
    cr
    wcel
    @23
    @18
    wa
    #
    @21
    @20
    cr
    @18
    @21
    @20
    wceq
    @23
    @18
    @20
    @3
    iftrue
    adantl
    #
    @23
    @20
    cr
    wcel
    @18
    @23
    @19
    c1
    @23
    @19
    @3
    @4
    @23
    cF
    @6
    wcel
    #
    @22
    @19
    @5
    wcel
    #
    wph
    @26
    @22
    ioorrnopnxrlem.f
    adantr
    wph
    @22
    simpr
    vi
    cX
    @5
    cF
    fvixp2
    syl2anc
    #
    elioored
    #
    @23
    1red
    #
    resubcld
    adantr
    eqeltrd
    #
    @23
    @18
    wn
    #
    wa
    #
    @21
    @3
    cr
    @32
    @21
    @3
    wceq
    @23
    @18
    @20
    @3
    iffalse
    adantl
    #
    @23
    @32
    @3
    cmnf
    wne
    #
    @3
    cr
    wcel
    @32
    @35
    @23
    @3
    cmnf
    neqne
    adantl
    @23
    @35
    wa
    @3
    @23
    @3
    cxr
    wcel
    #
    @35
    wph
    cX
    cxr
    @2
    cA
    ioorrnopnxrlem.a
    ffvelrnda
    #
    adantr
    @23
    @35
    simpr
    @23
    @3
    cpnf
    wne
    @35
    @23
    @3
    cpnf
    @37
    cpnf
    cxr
    wcel
    @23
    pnfxr
    a1i
    #
    @23
    @3
    @19
    cpnf
    @37
    @23
    @19
    @29
    rexrd
    #
    @38
    @23
    @36
    @4
    cxr
    wcel
    #
    @27
    @3
    @19
    clt
    wbr
    #
    @37
    wph
    cX
    cxr
    @2
    cB
    ioorrnopnxrlem.b
    ffvelrnda
    #
    @28
    @3
    @4
    @19
    ioogtlb
    syl3anc
    #
    @23
    @19
    @29
    ltpnfd
    xrlttrd
    xrltned
    adantr
    xrred
    syldan
    #
    eqeltrd
    pm2.61dan
    #
    ioorrnopnxrlem.l
    fmptd
    #
    wph
    vi
    cX
    @4
    cpnf
    wceq
    #
    @19
    c1
    caddc
    co
    #
    @4
    cif
    #
    cr
    cR
    @23
    @47
    @49
    cr
    wcel
    @23
    @47
    wa
    #
    @49
    @48
    cr
    @47
    @49
    @48
    wceq
    @23
    @47
    @48
    @4
    iftrue
    adantl
    #
    @23
    @48
    cr
    wcel
    @47
    @23
    @19
    c1
    @29
    @30
    readdcld
    adantr
    #
    eqeltrd
    @23
    @47
    wn
    #
    wa
    #
    @49
    @4
    cr
    @53
    @49
    @4
    wceq
    @23
    @47
    @48
    @4
    iffalse
    adantl
    #
    @23
    @53
    @4
    cpnf
    wne
    #
    @4
    cr
    wcel
    @53
    @56
    @23
    @4
    cpnf
    neqne
    adantl
    @23
    @56
    wa
    @4
    @23
    @40
    @56
    @42
    adantr
    @23
    @4
    cmnf
    wne
    @56
    @23
    cmnf
    @4
    cmnf
    cxr
    wcel
    @23
    mnfxr
    a1i
    #
    @42
    @23
    cmnf
    @19
    @4
    @57
    @39
    @42
    @23
    @19
    @29
    mnfltd
    @23
    @36
    @40
    @27
    @19
    @4
    clt
    wbr
    #
    @37
    @42
    @28
    @3
    @4
    @19
    iooltub
    syl3anc
    #
    xrlttrd
    xrgtned
    adantr
    @23
    @56
    simpr
    xrred
    syldan
    eqeltrd
    pm2.61dan
    #
    ioorrnopnxrlem.r
    fmptd
    #
    ioorrnopn
    eqeltrd
    wph
    @1
    @7
    wph
    cF
    @16
    cV
    wph
    cF
    cvv
    wcel
    #
    cF
    cX
    wfn
    #
    @19
    @15
    wcel
    #
    vi
    cX
    wral
    #
    w3a
    cF
    @16
    wcel
    wph
    @62
    @63
    @65
    wph
    cF
    @6
    ioorrnopnxrlem.f
    elexd
    wph
    @26
    @63
    ioorrnopnxrlem.f
    vi
    cX
    @5
    cF
    ixpfn
    syl
    wph
    @64
    vi
    cX
    @23
    @13
    @14
    @19
    @23
    @13
    wph
    cX
    cr
    @2
    cL
    @46
    ffvelrnda
    rexrd
    #
    @23
    @14
    wph
    cX
    cr
    @2
    cR
    @61
    ffvelrnda
    #
    rexrd
    #
    @29
    @23
    @18
    @13
    @19
    clt
    wbr
    @24
    @13
    @20
    @19
    clt
    @24
    @13
    @21
    @20
    @23
    @13
    @21
    wceq
    #
    @18
    wph
    vi
    cX
    @21
    cL
    cvv
    cL
    vi
    cX
    @21
    cmpt
    wceq
    wph
    ioorrnopnxrlem.l
    a1i
    @23
    @21
    cr
    @45
    elexd
    fvmpt2d
    #
    adantr
    @25
    eqtrd
    #
    @23
    @20
    @19
    clt
    wbr
    @18
    @23
    @19
    @29
    ltm1d
    adantr
    eqbrtrd
    @33
    @13
    @3
    @19
    clt
    @33
    @13
    @21
    @3
    @23
    @69
    @32
    @70
    adantr
    @34
    eqtrd
    #
    @23
    @41
    @32
    @43
    adantr
    eqbrtrd
    pm2.61dan
    @23
    @47
    @19
    @14
    clt
    wbr
    @50
    @19
    @48
    @14
    clt
    @23
    @19
    @48
    clt
    wbr
    @47
    @23
    @19
    @29
    ltp1d
    adantr
    @50
    @14
    @48
    @50
    @14
    @49
    @48
    @23
    @14
    @49
    wceq
    #
    @47
    wph
    vi
    cX
    @49
    cR
    cvv
    cR
    vi
    cX
    @49
    cmpt
    wceq
    wph
    ioorrnopnxrlem.r
    a1i
    @23
    @49
    cr
    @60
    elexd
    fvmpt2d
    #
    adantr
    @51
    eqtrd
    #
    eqcomd
    breqtrd
    @54
    @19
    @4
    @14
    clt
    @23
    @58
    @53
    @59
    adantr
    @54
    @14
    @4
    @54
    @14
    @49
    @4
    @23
    @73
    @53
    @74
    adantr
    @55
    eqtrd
    #
    eqcomd
    breqtrd
    pm2.61dan
    eliood
    ralrimiva
    3jca
    vi
    cX
    @15
    cF
    elixp2
    sylibr
    ioorrnopnxrlem.v
    syl6eleqr
    wph
    cV
    @16
    @6
    @17
    wph
    @15
    @5
    wss
    #
    vi
    cX
    wral
    @16
    @6
    wss
    wph
    @77
    vi
    cX
    @23
    @36
    @40
    @3
    @13
    cle
    wbr
    #
    @14
    @4
    cle
    wbr
    #
    @77
    @37
    @42
    @23
    @18
    @78
    @24
    @3
    @13
    @23
    @36
    @18
    @37
    adantr
    @23
    @13
    cxr
    wcel
    @18
    @66
    adantr
    @24
    @3
    @13
    clt
    wbr
    cmnf
    @20
    clt
    wbr
    @24
    cmnf
    @21
    @20
    clt
    @24
    @21
    @31
    mnfltd
    @25
    breqtrd
    @24
    @3
    cmnf
    @13
    @20
    clt
    @23
    @18
    simpr
    @71
    breq12d
    mpbird
    xrltled
    @33
    @3
    @13
    @44
    @33
    @13
    @3
    @72
    eqcomd
    eqled
    pm2.61dan
    @23
    @47
    @79
    @50
    @14
    @4
    @23
    @14
    cxr
    wcel
    @47
    @68
    adantr
    @23
    @40
    @47
    @42
    adantr
    @50
    @14
    @4
    clt
    wbr
    @48
    cpnf
    clt
    wbr
    @50
    @48
    @52
    ltpnfd
    @50
    @14
    @48
    @4
    cpnf
    clt
    @75
    @23
    @47
    simpr
    breq12d
    mpbird
    xrltled
    @54
    @14
    @4
    @23
    @14
    cr
    wcel
    @53
    @67
    adantr
    @76
    eqled
    pm2.61dan
    @3
    @4
    @13
    @14
    ioossioo
    syl22anc
    ralrimiva
    vi
    cX
    @15
    @5
    ss2ixp
    syl
    eqsstrd
    jca
    @12
    @8
    vv
    cV
    @0
    @9
    cV
    wceq
    @10
    @1
    @11
    @7
    @9
    cV
    cF
    eleq2
    @9
    cV
    @6
    sseq1
    anbi12d
    rspcev
    syl2anc
end
