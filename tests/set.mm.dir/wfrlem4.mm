include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wfn.mm"
include "cfv.mm"
include "cpred.mm"
include "wceq.mm"
include "wral.mm"
include "wfun.mm"
include "wfrlem2.mm"
include "funfn.mm"
include "sylib.mm"
include "fnresin1.mm"
include "syl.mm"
include "adantr.mm"
include "inss1.mm"
include "sseli.mm"
include "wss.mm"
include "w3a.mm"
include "wex.mm"
include "wi.mm"
include "wfrlem1.mm"
include "abeq2i.mm"
include "fndm.mm"
include "raleqdv.mm"
include "biimpar.mm"
include "rsp.mm"
include "3adant2.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl5.mm"
include "imp.mm"
include "adantlr.mm"
include "fvres.mm"
include "adantl.mm"
include "resres.mm"
include "predss.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "3an6.mm"
include "2exbii.mm"
include "eeanv.mm"
include "bitri.mm"
include "ssinss1.mm"
include "ad2antrr.mm"
include "nfra1.mm"
include "nfan.mm"
include "syl5com.mm"
include "inss2.mm"
include "anim12d.mm"
include "ssin.mm"
include "biimpi.mm"
include "syl6com.mm"
include "ralrimi.mm"
include "ad2ant2l.mm"
include "jca.mm"
include "wb.mm"
include "ineqan12d.mm"
include "sseq1.mm"
include "sseq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "mpbiri.mm"
include "3adant3.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "simpr.mm"
include "preddowncl.mm"
include "sylc.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"

theorem wfrlem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume wfrlem4.1: |- R We A
  assume wfrlem4.2: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( F ` ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint A a
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint B a
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint R a
  disjoint R f
  disjoint R g
  disjoint R h
  disjoint R x
  disjoint R y
  disjoint A b
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint F b
  disjoint F c
  disjoint R b
  disjoint R c
  assert |- ( ( g e. B /\ h e. B ) -> ( ( g |` ( dom g i^i dom h ) ) Fn ( dom g i^i dom h ) /\ A. a e. ( dom g i^i dom h ) ( ( g |` ( dom g i^i dom h ) ) ` a ) = ( F ` ( ( g |` ( dom g i^i dom h ) ) |` Pred ( R , ( dom g i^i dom h ) , a ) ) ) ) )

  proof
    vg
    cv
    #
    cB
    wcel
    #
    vh
    cv
    #
    cB
    wcel
    #
    wa
    #
    @0
    @0
    cdm
    #
    @2
    cdm
    #
    cin
    #
    cres
    #
    @7
    wfn
    #
    va
    cv
    #
    @8
    cfv
    #
    @8
    @7
    cR
    @10
    cpred
    #
    cres
    #
    cF
    cfv
    #
    wceq
    #
    va
    @7
    wral
    @1
    @9
    @3
    @1
    @0
    @5
    wfn
    #
    @9
    @1
    @0
    wfun
    @16
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    cF
    wfrlem4.2
    wfrlem2
    @0
    funfn
    sylib
    @5
    @6
    @0
    fnresin1
    syl
    adantr
    @4
    @15
    va
    @7
    @4
    @10
    @7
    wcel
    #
    wa
    #
    @10
    @0
    cfv
    #
    @0
    cA
    cR
    @10
    cpred
    #
    cres
    #
    cF
    cfv
    #
    @11
    @14
    @1
    @17
    @19
    @22
    wceq
    #
    @3
    @1
    @17
    @23
    @17
    @10
    @5
    wcel
    #
    @1
    @23
    @7
    @5
    @10
    @5
    @6
    inss1
    sseli
    @1
    @0
    vb
    cv
    #
    wfn
    #
    @25
    cA
    wss
    #
    @20
    @25
    wss
    #
    va
    @25
    wral
    #
    wa
    #
    @23
    va
    @25
    wral
    #
    w3a
    #
    vb
    wex
    #
    @24
    @23
    wi
    #
    @33
    vg
    cB
    vx
    vy
    vb
    va
    cA
    cB
    cR
    vf
    vg
    cF
    wfrlem4.2
    wfrlem1
    abeq2i
    #
    @32
    @34
    vb
    @26
    @31
    @34
    @30
    @26
    @31
    wa
    @23
    va
    @5
    wral
    #
    @34
    @26
    @36
    @31
    @26
    @23
    va
    @5
    @25
    @25
    @0
    fndm
    #
    raleqdv
    biimpar
    @23
    va
    @5
    rsp
    syl
    3adant2
    exlimiv
    sylbi
    syl5
    imp
    adantlr
    @17
    @11
    @19
    wceq
    @4
    @10
    @7
    @0
    fvres
    adantl
    @18
    @13
    @21
    cF
    @18
    @13
    @0
    @7
    @12
    cin
    #
    cres
    @21
    @0
    @7
    @12
    resres
    @18
    @38
    @20
    @0
    @18
    @38
    @12
    @20
    @12
    @7
    wss
    @38
    @12
    wceq
    @7
    cR
    @10
    predss
    @12
    @7
    sseqin2
    mpbi
    @18
    @7
    cA
    wss
    #
    @20
    @7
    wss
    #
    va
    @7
    wral
    #
    wa
    #
    @17
    @12
    @20
    wceq
    @4
    @42
    @17
    @1
    @33
    @2
    vc
    cv
    #
    wfn
    #
    @43
    cA
    wss
    #
    @20
    @43
    wss
    #
    va
    @43
    wral
    #
    wa
    #
    @10
    @2
    cfv
    @2
    @20
    cres
    cF
    cfv
    wceq
    va
    @43
    wral
    #
    w3a
    #
    vc
    wex
    #
    @42
    @3
    @35
    @51
    vh
    cB
    vx
    vy
    vc
    va
    cA
    cB
    cR
    vf
    vh
    cF
    wfrlem4.2
    wfrlem1
    abeq2i
    @33
    @51
    wa
    #
    @26
    @44
    wa
    #
    @30
    @48
    wa
    #
    @31
    @49
    wa
    #
    w3a
    #
    vc
    wex
    vb
    wex
    #
    @42
    @57
    @32
    @50
    wa
    #
    vc
    wex
    vb
    wex
    @52
    @56
    @58
    vb
    vc
    @26
    @44
    @30
    @48
    @31
    @49
    3an6
    2exbii
    @32
    @50
    vb
    vc
    eeanv
    bitri
    @56
    @42
    vb
    vc
    @53
    @54
    @42
    @55
    @53
    @54
    @42
    @53
    @54
    @42
    wi
    #
    @54
    @25
    @43
    cin
    #
    cA
    wss
    #
    @20
    @60
    wss
    #
    va
    @60
    wral
    #
    wa
    #
    wi
    #
    @54
    @61
    @63
    @27
    @61
    @29
    @48
    @25
    @43
    cA
    ssinss1
    ad2antrr
    @29
    @47
    @63
    @27
    @45
    @29
    @47
    wa
    #
    @62
    va
    @60
    @29
    @47
    va
    @28
    va
    @25
    nfra1
    @46
    va
    @43
    nfra1
    nfan
    @10
    @60
    wcel
    #
    @66
    @28
    @46
    wa
    #
    @62
    @67
    @29
    @28
    @47
    @46
    @67
    @10
    @25
    wcel
    @29
    @28
    @60
    @25
    @10
    @25
    @43
    inss1
    sseli
    @28
    va
    @25
    rsp
    syl5com
    @67
    @10
    @43
    wcel
    @47
    @46
    @60
    @43
    @10
    @25
    @43
    inss2
    sseli
    @46
    va
    @43
    rsp
    syl5com
    anim12d
    @68
    @62
    @20
    @25
    @43
    ssin
    biimpi
    syl6com
    ralrimi
    ad2ant2l
    jca
    @53
    @7
    @60
    wceq
    #
    @59
    @65
    wb
    @26
    @44
    @5
    @25
    @6
    @43
    @37
    @43
    @2
    fndm
    ineqan12d
    @69
    @42
    @64
    @54
    @69
    @39
    @61
    @41
    @63
    @7
    @60
    cA
    sseq1
    @40
    @62
    va
    @7
    @60
    @7
    @60
    @20
    sseq2
    raleqbi1dv
    anbi12d
    imbi2d
    syl
    mpbiri
    imp
    3adant3
    exlimivv
    sylbir
    syl2anb
    adantr
    @4
    @17
    simpr
    va
    cA
    @7
    cR
    @10
    preddowncl
    sylc
    syl5eq
    reseq2d
    syl5eq
    fveq2d
    3eqtr4d
    ralrimiva
    jca
end
