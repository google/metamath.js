include "cdm.mm"
include "cep.mm"
include "wor.mm"
include "crn.mm"
include "wpo.mm"
include "wfo.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wiso.mm"
include "con0.mm"
include "wss.mm"
include "cin.mm"
include "wf.mm"
include "wceq.mm"
include "ordtypelem4.mm"
include "fdm.mm"
include "syl.mm"
include "inss1.mm"
include "word.mm"
include "ordtypelem2.mm"
include "ordsson.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "wwe.mm"
include "epweon.mm"
include "weso.mm"
include "ax-mp.mm"
include "soss.mm"
include "mpisyl.mm"
include "frn.mm"
include "wess.mm"
include "sylc.mm"
include "sopo.mm"
include "3syl.mm"
include "wfun.mm"
include "ffun.mm"
include "funforn.mm"
include "sylib.mm"
include "wcel.mm"
include "wa.mm"
include "epel.mm"
include "ordtypelem6.mm"
include "syl5bi.mm"
include "ralrimiva.mm"
include "ralrimivw.mm"
include "soisoi.mm"
include "syl22anc.mm"

theorem ordtypelem8
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
  assert |- ( ph -> O Isom _E , R ( dom O , ran O ) )

  proof
    wph
    cO
    cdm
    #
    cep
    wor
    #
    cO
    crn
    #
    cR
    wpo
    #
    @0
    @2
    cO
    wfo
    #
    va
    cv
    #
    vb
    cv
    #
    cep
    wbr
    #
    @5
    cO
    cfv
    @6
    cO
    cfv
    cR
    wbr
    #
    wi
    #
    vb
    @0
    wral
    #
    va
    @0
    wral
    @0
    @2
    cep
    cR
    cO
    wiso
    wph
    @0
    con0
    wss
    con0
    cep
    wor
    #
    @1
    wph
    @0
    cT
    cF
    cdm
    #
    cin
    #
    con0
    wph
    @13
    cA
    cO
    wf
    #
    @0
    @13
    wceq
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
    #
    @13
    cA
    cO
    fdm
    syl
    wph
    @13
    cT
    con0
    cT
    @12
    inss1
    wph
    cT
    word
    cT
    con0
    wss
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
    cT
    ordsson
    syl
    syl5ss
    eqsstrd
    con0
    cep
    wwe
    @11
    epweon
    con0
    cep
    weso
    ax-mp
    @0
    con0
    cep
    soss
    mpisyl
    wph
    @2
    cR
    wwe
    #
    @2
    cR
    wor
    @3
    wph
    @2
    cA
    wss
    #
    cA
    cR
    wwe
    @16
    wph
    @14
    @17
    @15
    @13
    cA
    cO
    frn
    syl
    ordtypelem.7
    @2
    cA
    cR
    wess
    sylc
    @2
    cR
    weso
    @2
    cR
    sopo
    3syl
    wph
    cO
    wfun
    #
    @4
    wph
    @14
    @18
    @15
    @13
    cA
    cO
    ffun
    syl
    cO
    funforn
    sylib
    wph
    @10
    va
    @0
    wph
    @9
    vb
    @0
    @7
    @5
    @6
    wcel
    wph
    @6
    @0
    wcel
    wa
    @8
    va
    vb
    epel
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
    @6
    @5
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem6
    syl5bi
    ralrimiva
    ralrimivw
    va
    vb
    @0
    @2
    cep
    cR
    cO
    soisoi
    syl22anc
end
