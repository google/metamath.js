include "coi.mm"
include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "crio.mm"
include "cmpt.mm"
include "crecs.mm"
include "cima.mm"
include "wrex.mm"
include "con0.mm"
include "cres.mm"
include "c0.mm"
include "cif.mm"
include "df-oi.mm"
include "wceq.mm"
include "wcel.mm"
include "a1i.mm"
include "raleqdv.mm"
include "riotaeqbidv.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "recseq.mm"
include "ax-mp.mm"
include "imaeq1i.mm"
include "raleqi.mm"
include "rexbii.mm"
include "rabbii.mm"
include "reseq12i.mm"
include "ifeq1.mm"
include "eqtr4i.mm"

theorem dfoi
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cR: class R
  let vh: setvar h
  let vj: setvar j
  let cF: class F
  let cG: class G
  assume dfoi.1: |- C = { w e. A | A. j e. ran h j R w }
  assume dfoi.2: |- G = ( h e. _V |-> ( iota_ v e. C A. u e. C -. u R v ) )
  assume dfoi.3: |- F = recs ( G )

  disjoint h j
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h z
  disjoint A h
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint A j
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint F z
  disjoint R h
  disjoint R j
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R z
  assert |- OrdIso ( R , A ) = if ( ( R We A /\ R Se A ) , ( F |` { x e. On | E. t e. A A. z e. ( F " x ) z R t } ) , (/) )

  proof
    cA
    cR
    coi
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    #
    vh
    cvv
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
    vw
    cv
    cR
    wbr
    vj
    vh
    cv
    #
    crn
    wral
    vw
    cA
    crab
    #
    wral
    #
    vv
    @3
    crio
    #
    cmpt
    #
    crecs
    #
    vz
    cv
    vt
    cv
    cR
    wbr
    #
    vz
    @7
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
    cres
    #
    c0
    cif
    #
    @0
    cF
    @8
    vz
    cF
    @9
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
    cres
    #
    c0
    cif
    #
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cR
    vh
    vj
    df-oi
    @20
    @14
    wceq
    @21
    @15
    wceq
    cF
    @7
    @19
    @13
    cF
    cG
    crecs
    #
    @7
    dfoi.3
    cG
    @6
    wceq
    @22
    @7
    wceq
    cG
    vh
    cvv
    @1
    vu
    cC
    wral
    #
    vv
    cC
    crio
    #
    cmpt
    @6
    dfoi.2
    vh
    cvv
    @24
    @5
    @2
    cvv
    wcel
    #
    @23
    @4
    vv
    cC
    @3
    cC
    @3
    wceq
    @25
    dfoi.1
    a1i
    #
    @25
    @1
    vu
    cC
    @3
    @26
    raleqdv
    riotaeqbidv
    mpteq2ia
    eqtri
    cG
    @6
    recseq
    ax-mp
    eqtri
    #
    @18
    @12
    vx
    con0
    @17
    @11
    vt
    cA
    @8
    vz
    @16
    @10
    cF
    @7
    @9
    @27
    imaeq1i
    raleqi
    rexbii
    rabbii
    reseq12i
    @0
    @20
    @14
    c0
    ifeq1
    ax-mp
    eqtr4i
end
