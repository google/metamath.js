include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "wss.mm"
include "ccom.mm"
include "cvv.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cxp.mm"
include "ciun.mm"
include "dfco2.mm"
include "wcel.mm"
include "wrex.mm"
include "wex.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "vex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "brelrn.mm"
include "sylbi.mm"
include "elimasn.mm"
include "opeldm.mm"
include "anim12ci.mm"
include "adantl.mm"
include "exlimivv.mm"
include "elxp.mm"
include "elin.mm"
include "3imtr4i.mm"
include "ssel.mm"
include "syl5.mm"
include "pm4.71rd.mm"
include "exbidv.mm"
include "rexv.mm"
include "df-rex.mm"
include "3bitr4g.mm"
include "eliun.mm"
include "eqrdv.mm"
include "syl5eq.mm"

theorem dfco2a
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  assert |- ( ( dom A i^i ran B ) C_ C -> ( A o. B ) = U_ x e. C ( ( `' B " { x } ) X. ( A " { x } ) ) )

  proof
    cA
    cdm
    #
    cB
    crn
    #
    cin
    #
    cC
    wss
    #
    cA
    cB
    ccom
    vx
    cvv
    cB
    ccnv
    vx
    cv
    #
    csn
    #
    cima
    #
    cA
    @5
    cima
    #
    cxp
    #
    ciun
    #
    vx
    cC
    @8
    ciun
    #
    vx
    cA
    cB
    dfco2
    @3
    vy
    @9
    @10
    @3
    vy
    cv
    #
    @8
    wcel
    #
    vx
    cvv
    wrex
    #
    @12
    vx
    cC
    wrex
    #
    @11
    @9
    wcel
    @11
    @10
    wcel
    @3
    @12
    vx
    wex
    @4
    cC
    wcel
    #
    @12
    wa
    #
    vx
    wex
    @13
    @14
    @3
    @12
    @16
    vx
    @3
    @12
    @15
    @12
    @4
    @2
    wcel
    #
    @3
    @15
    @11
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    #
    @18
    @6
    wcel
    #
    @19
    @7
    wcel
    #
    wa
    #
    wa
    #
    vw
    wex
    vz
    wex
    @4
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @12
    @17
    @24
    @27
    vz
    vw
    @23
    @27
    @20
    @21
    @26
    @22
    @25
    @21
    @18
    @4
    cB
    wbr
    #
    @26
    @4
    cvv
    wcel
    @21
    @28
    wb
    vx
    vex
    #
    cB
    @4
    @18
    cvv
    vz
    vex
    #
    eliniseg
    ax-mp
    @18
    @4
    cB
    @30
    @29
    brelrn
    sylbi
    @22
    @4
    @19
    cop
    cA
    wcel
    @25
    cA
    @4
    @19
    @29
    vw
    vex
    #
    elimasn
    @4
    @19
    cA
    @29
    @31
    opeldm
    sylbi
    anim12ci
    adantl
    exlimivv
    vz
    vw
    @11
    @6
    @7
    elxp
    @4
    @0
    @1
    elin
    3imtr4i
    @2
    cC
    @4
    ssel
    syl5
    pm4.71rd
    exbidv
    @12
    vx
    rexv
    @12
    vx
    cC
    df-rex
    3bitr4g
    vx
    @11
    cvv
    @8
    eliun
    vx
    @11
    cC
    @8
    eliun
    3bitr4g
    eqrdv
    syl5eq
end
