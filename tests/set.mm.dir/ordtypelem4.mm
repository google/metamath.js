include "cdm.mm"
include "cin.mm"
include "wf.mm"
include "cres.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wfun.mm"
include "wlim.mm"
include "tfr1a.mm"
include "simpli.mm"
include "funres.mm"
include "mp1i.mm"
include "funfn.mm"
include "sylib.mm"
include "dmres.mm"
include "fneq2i.mm"
include "wa.mm"
include "wceq.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "fvres.mm"
include "syl.mm"
include "wbr.mm"
include "wn.mm"
include "cima.mm"
include "crab.mm"
include "ssrab2.mm"
include "sstri.mm"
include "ordtypelem3.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "ordtypelem1.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem ordtypelem4
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
  let cO: class O
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let va: setvar a
  let cM: class M
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
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
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
  disjoint M h
  disjoint M j
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M z
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
  assert |- ( ph -> O : ( T i^i dom F ) --> A )

  proof
    wph
    cT
    cF
    cdm
    #
    cin
    #
    cA
    cO
    wf
    @1
    cA
    cF
    cT
    cres
    #
    wf
    #
    wph
    @2
    @1
    wfn
    #
    va
    cv
    #
    @2
    cfv
    #
    cA
    wcel
    #
    va
    @1
    wral
    @3
    wph
    @2
    @2
    cdm
    #
    wfn
    #
    @4
    wph
    @2
    wfun
    #
    @9
    cF
    wfun
    #
    @10
    wph
    @11
    @0
    wlim
    cF
    cG
    ordtypelem.1
    tfr1a
    simpli
    cT
    cF
    funres
    mp1i
    @2
    funfn
    sylib
    @8
    @1
    @2
    cF
    cT
    dmres
    fneq2i
    sylib
    wph
    @7
    va
    @1
    wph
    @5
    @1
    wcel
    #
    wa
    #
    @6
    @5
    cF
    cfv
    #
    cA
    @13
    @5
    cT
    wcel
    @6
    @14
    wceq
    @13
    @1
    cT
    @5
    cT
    @0
    inss1
    wph
    @12
    simpr
    sseldi
    @5
    cT
    cF
    fvres
    syl
    @13
    vu
    cv
    vv
    cv
    cR
    wbr
    wn
    vu
    vj
    cv
    vw
    cv
    cR
    wbr
    vj
    cF
    @5
    cima
    wral
    #
    vw
    cA
    crab
    #
    wral
    #
    vv
    @16
    crab
    #
    cA
    @14
    @18
    @16
    cA
    @17
    vv
    @16
    ssrab2
    @15
    vw
    cA
    ssrab2
    sstri
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
    @5
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem3
    sseldi
    eqeltrd
    ralrimiva
    va
    @1
    cA
    @2
    ffnfv
    sylanbrc
    wph
    @1
    cA
    cO
    @2
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
    feq1d
    mpbird
end
