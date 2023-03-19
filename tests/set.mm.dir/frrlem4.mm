include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wfn.mm"
include "cfv.mm"
include "cpred.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wfun.mm"
include "frrlem2.mm"
include "funfn.mm"
include "sylib.mm"
include "fnresin1.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "w3a.mm"
include "wex.mm"
include "wi.mm"
include "frrlem1.mm"
include "abeq2i.mm"
include "fndm.mm"
include "raleqdv.mm"
include "biimp3ar.mm"
include "rsp.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "elinel1.mm"
include "impel.mm"
include "adantlr.mm"
include "simpr.mm"
include "fvresd.mm"
include "resres.mm"
include "predss.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "eeanv.mm"
include "inss1.mm"
include "simpl2l.mm"
include "syl5ss.mm"
include "simp2r.mm"
include "nfra1.mm"
include "nfan.mm"
include "wel.mm"
include "syl5com.mm"
include "elinel2.mm"
include "anim12d.mm"
include "ssin.mm"
include "biimpi.mm"
include "syl6com.mm"
include "ralrimi.mm"
include "syl2an.mm"
include "wb.mm"
include "simpl1.mm"
include "simpr1.mm"
include "ineq12.mm"
include "sseq1d.mm"
include "sseq2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "preddowncl.mm"
include "sylc.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "jca.mm"

theorem frrlem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume frrlem4.1: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint A a
  disjoint A f
  disjoint A g
  disjoint a f
  disjoint a g
  disjoint f g
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint B a
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint G a
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint g x
  disjoint g y
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
  disjoint b f
  disjoint c f
  disjoint b g
  disjoint c g
  disjoint b c
  disjoint b h
  disjoint c h
  disjoint b x
  disjoint c x
  disjoint b y
  disjoint c y
  disjoint G b
  disjoint G c
  disjoint R b
  disjoint R c
  assert |- ( ( g e. B /\ h e. B ) -> ( ( g |` ( dom g i^i dom h ) ) Fn ( dom g i^i dom h ) /\ A. a e. ( dom g i^i dom h ) ( ( g |` ( dom g i^i dom h ) ) ` a ) = ( a G ( ( g |` ( dom g i^i dom h ) ) |` Pred ( R , ( dom g i^i dom h ) , a ) ) ) ) )

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
    @10
    @8
    @7
    cR
    @10
    cpred
    #
    cres
    #
    cG
    co
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
    cG
    frrlem4.1
    frrlem2
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
    @10
    @0
    cA
    cR
    @10
    cpred
    #
    cres
    #
    cG
    co
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
    @10
    @5
    wcel
    #
    @23
    @17
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
    cG
    frrlem4.1
    frrlem1
    abeq2i
    #
    @32
    @34
    vb
    @32
    @23
    va
    @5
    wral
    #
    @34
    @26
    @30
    @36
    @31
    @26
    @30
    wa
    @23
    va
    @5
    @25
    @26
    @5
    @25
    wceq
    #
    @30
    @25
    @0
    fndm
    #
    adantr
    raleqdv
    biimp3ar
    @23
    va
    @5
    rsp
    syl
    exlimiv
    sylbi
    @10
    @5
    @6
    elinel1
    impel
    adantlr
    @18
    @10
    @7
    @0
    @4
    @17
    simpr
    #
    fvresd
    @18
    @13
    @21
    @10
    cG
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
    @40
    @20
    @0
    @18
    @40
    @12
    @20
    @12
    @7
    wss
    @40
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
    @44
    @17
    @1
    @33
    @2
    vc
    cv
    #
    wfn
    #
    @45
    cA
    wss
    #
    @20
    @45
    wss
    #
    va
    @45
    wral
    #
    wa
    #
    @10
    @2
    cfv
    @10
    @2
    @20
    cres
    cG
    co
    wceq
    va
    @45
    wral
    #
    w3a
    #
    vc
    wex
    #
    @44
    @3
    @35
    @53
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
    cG
    frrlem4.1
    frrlem1
    abeq2i
    @33
    @53
    wa
    @32
    @52
    wa
    #
    vc
    wex
    vb
    wex
    @44
    @32
    @52
    vb
    vc
    eeanv
    @54
    @44
    vb
    vc
    @54
    @44
    @25
    @45
    cin
    #
    cA
    wss
    #
    @20
    @55
    wss
    #
    va
    @55
    wral
    #
    @54
    @55
    @25
    cA
    @25
    @45
    inss1
    @27
    @29
    @26
    @31
    @52
    simpl2l
    syl5ss
    @32
    @29
    @49
    @58
    @52
    @26
    @27
    @29
    @31
    simp2r
    @46
    @47
    @49
    @51
    simp2r
    @29
    @49
    wa
    #
    @57
    va
    @55
    @29
    @49
    va
    @28
    va
    @25
    nfra1
    @48
    va
    @45
    nfra1
    nfan
    @10
    @55
    wcel
    #
    @59
    @28
    @48
    wa
    #
    @57
    @60
    @29
    @28
    @49
    @48
    @60
    va
    vb
    wel
    @29
    @28
    @10
    @25
    @45
    elinel1
    @28
    va
    @25
    rsp
    syl5com
    @60
    va
    vc
    wel
    @49
    @48
    @10
    @25
    @45
    elinel2
    @48
    va
    @45
    rsp
    syl5com
    anim12d
    @61
    @57
    @20
    @25
    @45
    ssin
    biimpi
    syl6com
    ralrimi
    syl2an
    @54
    @37
    @6
    @45
    wceq
    #
    @44
    @56
    @58
    wa
    wb
    @54
    @26
    @37
    @26
    @30
    @31
    @52
    simpl1
    @38
    syl
    @54
    @46
    @62
    @32
    @46
    @50
    @51
    simpr1
    @45
    @2
    fndm
    syl
    @37
    @62
    wa
    #
    @41
    @56
    @43
    @58
    @63
    @7
    @55
    cA
    @5
    @25
    @6
    @45
    ineq12
    #
    sseq1d
    @63
    @42
    @57
    va
    @7
    @55
    @64
    @63
    @7
    @55
    @20
    @64
    sseq2d
    raleqbidv
    anbi12d
    syl2anc
    mpbir2and
    exlimivv
    sylbir
    syl2anb
    adantr
    @39
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
    oveq2d
    3eqtr4d
    ralrimiva
    jca
end
