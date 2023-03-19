include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "simprr.mm"
include "cima.mm"
include "crab.mm"
include "wn.mm"
include "ssrab2.mm"
include "cin.mm"
include "simpr.mm"
include "wceq.mm"
include "wf.mm"
include "ordtypelem4.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "ordtypelem3.mm"
include "syldan.mm"
include "sseldi.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "wfun.mm"
include "wlim.mm"
include "tfr1a.mm"
include "simpli.mm"
include "funfn.mm"
include "mpbi.mm"
include "word.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "ordelss.mm"
include "sylancr.mm"
include "breq1.mm"
include "ralima.mm"
include "mpbid.mm"
include "adantrr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cres.mm"
include "ordtypelem1.mm"
include "fveq1d.mm"
include "ordtypelem2.mm"
include "inss1.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "fvres.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "expr.mm"

theorem ordtypelem6
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
  let cN: class N
  let cO: class O
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
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
  disjoint N j
  disjoint N u
  disjoint N w
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
  assert |- ( ( ph /\ M e. dom O ) -> ( N e. M -> ( O ` N ) R ( O ` M ) ) )

  proof
    wph
    cM
    cO
    cdm
    #
    wcel
    #
    cN
    cM
    wcel
    #
    cN
    cO
    cfv
    #
    cM
    cO
    cfv
    #
    cR
    wbr
    wph
    @1
    @2
    wa
    #
    wa
    #
    cN
    cF
    cfv
    #
    cM
    cF
    cfv
    #
    @3
    @4
    cR
    @6
    @2
    va
    cv
    #
    cF
    cfv
    #
    @8
    cR
    wbr
    #
    va
    cM
    wral
    #
    @7
    @8
    cR
    wbr
    #
    wph
    @1
    @2
    simprr
    #
    wph
    @1
    @12
    @2
    wph
    @1
    wa
    #
    vj
    cv
    #
    @8
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
    @12
    @15
    @8
    @16
    vw
    cv
    #
    cR
    wbr
    #
    vj
    @18
    wral
    #
    vw
    cA
    crab
    #
    wcel
    #
    @19
    @15
    vu
    cv
    vv
    cv
    cR
    wbr
    wn
    vu
    @23
    wral
    #
    vv
    @23
    crab
    #
    @23
    @8
    @25
    vv
    @23
    ssrab2
    wph
    @1
    cM
    cT
    cF
    cdm
    #
    cin
    #
    wcel
    @8
    @26
    wcel
    @15
    cM
    @0
    @28
    wph
    @1
    simpr
    wph
    @0
    @28
    wceq
    #
    @1
    wph
    @28
    cA
    cO
    wf
    @29
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem4
    @28
    cA
    cO
    fdm
    syl
    #
    adantr
    eleqtrd
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cM
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem3
    syldan
    sseldi
    @24
    @8
    cA
    wcel
    @19
    @22
    @19
    vw
    @8
    cA
    @20
    @8
    wceq
    @21
    @17
    vj
    @18
    @20
    @8
    @16
    cR
    breq2
    ralbidv
    elrab
    simprbi
    syl
    @15
    cF
    @27
    wfn
    #
    cM
    @27
    wss
    #
    @19
    @12
    wb
    cF
    wfun
    #
    @31
    @33
    @27
    wlim
    #
    cF
    cG
    ordtypelem.1
    tfr1a
    #
    simpli
    cF
    funfn
    mpbi
    @15
    @27
    word
    #
    cM
    @27
    wcel
    @32
    @34
    @36
    @33
    @34
    @35
    simpri
    @27
    limord
    ax-mp
    wph
    @0
    @27
    cM
    wph
    @0
    @28
    @27
    @30
    cT
    @27
    inss2
    syl6eqss
    sselda
    @27
    cM
    ordelss
    sylancr
    @17
    @11
    vj
    va
    @27
    cM
    cF
    @16
    @10
    @8
    cR
    breq1
    ralima
    sylancr
    mpbid
    adantrr
    @11
    @13
    va
    cN
    cM
    @9
    cN
    wceq
    @10
    @7
    @8
    cR
    @9
    cN
    cF
    fveq2
    breq1d
    rspcv
    sylc
    @6
    @3
    cN
    cF
    cT
    cres
    #
    cfv
    #
    @7
    @6
    cN
    cO
    @37
    wph
    cO
    @37
    wceq
    @5
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem1
    adantr
    #
    fveq1d
    @6
    cN
    cT
    wcel
    @38
    @7
    wceq
    @6
    cM
    cT
    cN
    @6
    cT
    word
    #
    cM
    cT
    wcel
    #
    cM
    cT
    wss
    wph
    @40
    @5
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem2
    adantr
    wph
    @1
    @41
    @2
    wph
    @0
    cT
    cM
    wph
    @0
    @28
    cT
    @30
    cT
    @27
    inss1
    syl6eqss
    sselda
    adantrr
    #
    cT
    cM
    ordelss
    syl2anc
    @14
    sseldd
    cN
    cT
    cF
    fvres
    syl
    eqtrd
    @6
    @4
    cM
    @37
    cfv
    #
    @8
    @6
    cM
    cO
    @37
    @39
    fveq1d
    @6
    @41
    @43
    @8
    wceq
    @42
    cM
    cT
    cF
    fvres
    syl
    eqtrd
    3brtr4d
    expr
end
