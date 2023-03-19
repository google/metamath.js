include "wceq.mm"
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
include "coi.mm"
include "weeq2.mm"
include "seeq2.mm"
include "anbi12d.mm"
include "rabeq.mm"
include "raleqdv.mm"
include "riotaeqbidv.mm"
include "mpteq2dv.mm"
include "recseq.mm"
include "syl.mm"
include "imaeq1d.mm"
include "rexeqbi1dv.mm"
include "rabbidv.mm"
include "reseq12d.mm"
include "ifbieq1d.mm"
include "df-oi.mm"
include "3eqtr4g.mm"

theorem oieq2
  let cA: class A
  let cB: class B
  let cR: class R
  let vh: setvar h
  let vj: setvar j
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cS: class S


  assert |- ( A = B -> OrdIso ( R , A ) = OrdIso ( R , B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
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
    crn
    wral
    #
    vw
    cA
    crab
    #
    wral
    #
    vv
    @6
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
    @10
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
    cB
    cR
    wwe
    #
    cB
    cR
    wse
    #
    wa
    #
    vh
    cvv
    @4
    vu
    @5
    vw
    cB
    crab
    #
    wral
    #
    vv
    @21
    crio
    #
    cmpt
    #
    crecs
    #
    @11
    vz
    @25
    @12
    cima
    #
    wral
    #
    vt
    cB
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
    cA
    cR
    coi
    cB
    cR
    coi
    @0
    @3
    @20
    @17
    @30
    c0
    @0
    @1
    @18
    @2
    @19
    cA
    cB
    cR
    weeq2
    cA
    cB
    cR
    seeq2
    anbi12d
    @0
    @10
    @25
    @16
    @29
    @0
    @9
    @24
    wceq
    @10
    @25
    wceq
    @0
    vh
    cvv
    @8
    @23
    @0
    @7
    @22
    vv
    @6
    @21
    @5
    vw
    cA
    cB
    rabeq
    #
    @0
    @4
    vu
    @6
    @21
    @31
    raleqdv
    riotaeqbidv
    mpteq2dv
    @9
    @24
    recseq
    syl
    #
    @0
    @15
    @28
    vx
    con0
    @14
    @27
    vt
    cA
    cB
    @0
    @11
    vz
    @13
    @26
    @0
    @10
    @25
    @12
    @32
    imaeq1d
    raleqdv
    rexeqbi1dv
    rabbidv
    reseq12d
    ifbieq1d
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
    vx
    vz
    vw
    vv
    vu
    vt
    cB
    cR
    vh
    vj
    df-oi
    3eqtr4g
end
