include "wtr.mm"
include "word.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cima.mm"
include "wrex.mm"
include "con0.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "onss.mm"
include "syl.mm"
include "eloni.mm"
include "weq.mm"
include "imaeq2.mm"
include "raleqdv.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "adantl.mm"
include "wi.mm"
include "ordelss.mm"
include "imass2.mm"
include "ssralv.mm"
include "reximdv.mm"
include "3syl.mm"
include "ralrimdva.mm"
include "sylc.mm"
include "ssrab.mm"
include "sylanbrc.mm"
include "syl6sseqr.mm"
include "ralrimiva.mm"
include "dftr3.mm"
include "sylibr.mm"
include "ordon.mm"
include "trssord.mm"
include "mp3an23.mm"

theorem ordtypelem2
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
  assert |- ( ph -> Ord T )

  proof
    wph
    cT
    wtr
    #
    cT
    word
    #
    wph
    va
    cv
    #
    cT
    wss
    #
    va
    cT
    wral
    @0
    wph
    @3
    va
    cT
    wph
    @2
    cT
    wcel
    #
    wa
    #
    @2
    vz
    cv
    vt
    cv
    cR
    wbr
    #
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
    #
    vx
    con0
    crab
    #
    cT
    @5
    @2
    con0
    wss
    #
    @10
    vx
    @2
    wral
    #
    @2
    @11
    wss
    @5
    @2
    con0
    wcel
    #
    @12
    wph
    cT
    con0
    @2
    cT
    con0
    wss
    #
    wph
    cT
    @11
    con0
    ordtypelem.5
    @10
    vx
    con0
    ssrab2
    eqsstri
    #
    a1i
    sselda
    #
    @2
    onss
    syl
    @5
    @2
    word
    #
    @6
    vz
    cF
    @2
    cima
    #
    wral
    #
    vt
    cA
    wrex
    #
    @13
    @5
    @14
    @18
    @17
    @2
    eloni
    syl
    @4
    @21
    wph
    @4
    @14
    @21
    @10
    @21
    vx
    @2
    con0
    cT
    vx
    va
    weq
    #
    @9
    @20
    vt
    cA
    @22
    @6
    vz
    @8
    @19
    @7
    @2
    cF
    imaeq2
    raleqdv
    rexbidv
    ordtypelem.5
    elrab2
    simprbi
    adantl
    @18
    @21
    @10
    vx
    @2
    @18
    @7
    @2
    wcel
    wa
    @7
    @2
    wss
    @8
    @19
    wss
    #
    @21
    @10
    wi
    @2
    @7
    ordelss
    @7
    @2
    cF
    imass2
    @23
    @20
    @9
    vt
    cA
    @6
    vz
    @8
    @19
    ssralv
    reximdv
    3syl
    ralrimdva
    sylc
    @10
    vx
    con0
    @2
    ssrab
    sylanbrc
    ordtypelem.5
    syl6sseqr
    ralrimiva
    va
    cT
    dftr3
    sylibr
    @0
    @15
    con0
    word
    @1
    @16
    ordon
    cT
    con0
    trssord
    mp3an23
    syl
end
