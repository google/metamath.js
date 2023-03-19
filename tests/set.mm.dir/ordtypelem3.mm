include "cdm.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cima.mm"
include "wral.mm"
include "crab.mm"
include "crio.mm"
include "cres.mm"
include "wceq.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "tfr2a.mm"
include "syl.mm"
include "cvv.mm"
include "word.mm"
include "wb.mm"
include "wlim.mm"
include "wfun.mm"
include "tfr1a.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordelord.mm"
include "sylancr.mm"
include "tfr2b.mm"
include "mpbid.mm"
include "crn.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "riotaeqbidv.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "wreu.mm"
include "wwe.mm"
include "wse.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "adantr.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wrex.mm"
include "inss1.mm"
include "con0.mm"
include "imaeq2.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "breq1.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "rabn0.mm"
include "wereu2.mm"
include "syl22anc.mm"
include "riotacl2.mm"
include "eqeltrd.mm"

theorem ordtypelem3
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cR: class R
  let cT: class T
  let vh: setvar h
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cM: class M
  let cO: class O
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let vm: setvar m
  let vy: setvar y
  assume ordtypelem.1: |- F = recs ( G )
  assume ordtypelem.2: |- C = { w e. A | A. j e. ran h j R w }
  assume ordtypelem.3: |- G = ( h e. _V |-> ( iota_ v e. C A. u e. C -. u R v ) )
  assume ordtypelem.5: |- T = { x e. On | E. t e. A A. z e. ( F " x ) z R t }
  assume ordtypelem.6: |- O = OrdIso ( R , A )
  assume ordtypelem.7: |- ( ph -> R We A )
  assume ordtypelem.8: |- ( ph -> R Se A )

  disjoint u v
  disjoint C u
  disjoint C v
  disjoint h j
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h z
  disjoint M h
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint M j
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint M t
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint M v
  disjoint w x
  disjoint w z
  disjoint M w
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint R h
  disjoint R j
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R z
  disjoint A h
  disjoint A j
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A z
  disjoint O t
  disjoint O u
  disjoint O v
  disjoint O x
  disjoint ph t
  disjoint ph x
  disjoint F h
  disjoint F j
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F z
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint C f
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint C r
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint a h
  disjoint a j
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint M a
  disjoint a b
  disjoint N a
  disjoint b j
  disjoint b u
  disjoint b w
  disjoint N b
  disjoint N j
  disjoint N u
  disjoint N w
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a m
  disjoint a r
  disjoint a s
  disjoint a y
  disjoint R a
  disjoint b c
  disjoint b f
  disjoint b h
  disjoint b i
  disjoint b m
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c f
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint h i
  disjoint h m
  disjoint h r
  disjoint h s
  disjoint h y
  disjoint i j
  disjoint i m
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint j m
  disjoint j r
  disjoint j s
  disjoint j y
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint R m
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A m
  disjoint A r
  disjoint A s
  disjoint A y
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O m
  disjoint a ph
  disjoint b ph
  disjoint m ph
  disjoint F a
  disjoint F b
  disjoint F c
  assert |- ( ( ph /\ M e. ( T i^i dom F ) ) -> ( F ` M ) e. { v e. { w e. A | A. j e. ( F " M ) j R w } | A. u e. { w e. A | A. j e. ( F " M ) j R w } -. u R v } )

  proof
    wph
    cM
    cT
    cF
    cdm
    #
    cin
    #
    wcel
    #
    wa
    #
    cM
    cF
    cfv
    #
    vu
    cv
    vv
    cv
    cR
    wbr
    wn
    #
    vu
    vj
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    vj
    cF
    cM
    cima
    #
    wral
    #
    vw
    cA
    crab
    #
    wral
    #
    vv
    @11
    crio
    #
    @12
    vv
    @11
    crab
    #
    @3
    @4
    cF
    cM
    cres
    #
    cG
    cfv
    #
    @13
    @3
    cM
    @0
    wcel
    #
    @4
    @16
    wceq
    @3
    @1
    @0
    cM
    cT
    @0
    inss2
    wph
    @2
    simpr
    #
    sseldi
    #
    cM
    cF
    cG
    ordtypelem.1
    tfr2a
    syl
    @3
    @15
    cvv
    wcel
    #
    @16
    @13
    wceq
    @3
    @17
    @20
    @19
    @3
    cM
    word
    #
    @17
    @20
    wb
    @3
    @0
    word
    #
    @17
    @21
    @0
    wlim
    #
    @22
    cF
    wfun
    @23
    cF
    cG
    ordtypelem.1
    tfr1a
    simpri
    @0
    limord
    ax-mp
    @19
    @0
    cM
    ordelord
    sylancr
    cM
    cF
    cG
    ordtypelem.1
    tfr2b
    syl
    mpbid
    vh
    @15
    @5
    vu
    cC
    wral
    #
    vv
    cC
    crio
    @13
    cvv
    cG
    vh
    cv
    #
    @15
    wceq
    #
    @24
    @12
    vv
    cC
    @11
    @26
    cC
    @8
    vj
    @25
    crn
    #
    wral
    #
    vw
    cA
    crab
    @11
    ordtypelem.2
    @26
    @28
    @10
    vw
    cA
    @26
    @8
    vj
    @27
    @9
    @26
    @27
    @15
    crn
    @9
    @25
    @15
    rneq
    cF
    cM
    df-ima
    syl6eqr
    raleqdv
    rabbidv
    syl5eq
    #
    @26
    @5
    vu
    cC
    @11
    @29
    raleqdv
    riotaeqbidv
    ordtypelem.3
    @12
    vv
    @11
    riotaex
    fvmpt
    syl
    eqtrd
    @3
    @12
    vv
    @11
    wreu
    #
    @13
    @14
    wcel
    @3
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    @11
    cA
    wss
    #
    @11
    c0
    wne
    #
    @30
    wph
    @31
    @2
    ordtypelem.7
    adantr
    wph
    @32
    @2
    ordtypelem.8
    adantr
    @33
    @3
    @10
    vw
    cA
    ssrab2
    a1i
    @3
    @10
    vw
    cA
    wrex
    #
    @34
    @3
    vz
    cv
    #
    vt
    cv
    #
    cR
    wbr
    #
    vz
    @9
    wral
    #
    vt
    cA
    wrex
    #
    @35
    @3
    cM
    cT
    wcel
    #
    @40
    @3
    @1
    cT
    cM
    cT
    @0
    inss1
    @18
    sseldi
    @41
    cM
    con0
    wcel
    @40
    @38
    vz
    cF
    vx
    cv
    #
    cima
    #
    wral
    #
    vt
    cA
    wrex
    @40
    vx
    cM
    con0
    cT
    @42
    cM
    wceq
    #
    @44
    @39
    vt
    cA
    @45
    @38
    vz
    @43
    @9
    @42
    cM
    cF
    imaeq2
    raleqdv
    rexbidv
    ordtypelem.5
    elrab2
    simprbi
    syl
    @10
    @39
    vw
    vt
    cA
    @10
    @36
    @7
    cR
    wbr
    #
    vz
    @9
    wral
    @7
    @37
    wceq
    #
    @39
    @8
    @46
    vj
    vz
    @9
    @6
    @36
    @7
    cR
    breq1
    cbvralv
    @47
    @46
    @38
    vz
    @9
    @7
    @37
    @36
    cR
    breq2
    ralbidv
    syl5bb
    cbvrexv
    sylibr
    @10
    vw
    cA
    rabn0
    sylibr
    vv
    vu
    cA
    @11
    cR
    wereu2
    syl22anc
    @12
    vv
    @11
    riotacl2
    syl
    eqeltrd
end
