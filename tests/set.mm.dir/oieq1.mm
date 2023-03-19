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
include "weeq1.mm"
include "seeq1.mm"
include "anbi12d.mm"
include "breq.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "notbid.mm"
include "raleqbidv.mm"
include "riotaeqbidv.mm"
include "mpteq2dv.mm"
include "recseq.mm"
include "syl.mm"
include "imaeq1d.mm"
include "rexbidv.mm"
include "reseq12d.mm"
include "ifbieq1d.mm"
include "df-oi.mm"
include "3eqtr4g.mm"

theorem oieq1
  let cA: class A
  let cR: class R
  let cS: class S
  let vh: setvar h
  let vj: setvar j
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cB: class B


  assert |- ( R = S -> OrdIso ( R , A ) = OrdIso ( S , A ) )

  proof
    cR
    cS
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
    #
    vv
    cv
    #
    cR
    wbr
    #
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
    vh
    cv
    crn
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
    @13
    crio
    #
    cmpt
    #
    crecs
    #
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
    @17
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
    cA
    cS
    wwe
    #
    cA
    cS
    wse
    #
    wa
    #
    vh
    cvv
    @4
    @5
    cS
    wbr
    #
    wn
    #
    vu
    @8
    @9
    cS
    wbr
    #
    vj
    @11
    wral
    #
    vw
    cA
    crab
    #
    wral
    #
    vv
    @34
    crio
    #
    cmpt
    #
    crecs
    #
    @18
    @19
    cS
    wbr
    #
    vz
    @38
    @21
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
    cA
    cR
    coi
    cA
    cS
    coi
    @0
    @3
    @29
    @26
    @44
    c0
    @0
    @1
    @27
    @2
    @28
    cA
    cR
    cS
    weeq1
    cA
    cR
    cS
    seeq1
    anbi12d
    @0
    @17
    @38
    @25
    @43
    @0
    @16
    @37
    wceq
    @17
    @38
    wceq
    @0
    vh
    cvv
    @15
    @36
    @0
    @14
    @35
    vv
    @13
    @34
    @0
    @12
    @33
    vw
    cA
    @0
    @10
    @32
    vj
    @11
    @8
    @9
    cR
    cS
    breq
    ralbidv
    rabbidv
    #
    @0
    @7
    @31
    vu
    @13
    @34
    @45
    @0
    @6
    @30
    @4
    @5
    cR
    cS
    breq
    notbid
    raleqbidv
    riotaeqbidv
    mpteq2dv
    @16
    @37
    recseq
    syl
    #
    @0
    @24
    @42
    vx
    con0
    @0
    @23
    @41
    vt
    cA
    @0
    @20
    @39
    vz
    @22
    @40
    @0
    @17
    @38
    @21
    @46
    imaeq1d
    @18
    @19
    cR
    cS
    breq
    raleqbidv
    rexbidv
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
    cA
    cS
    vh
    vj
    df-oi
    3eqtr4g
end
