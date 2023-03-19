include "cab.mm"
include "cint.mm"
include "wrel.mm"
include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "crab.mm"
include "cnvcnv.mm"
include "incom.mm"
include "eqtri.mm"
include "dfrel2.mm"
include "biimpi.mm"
include "relintabex.mm"
include "xpinintabd.mm"
include "eqtr4i.mm"
include "eqeq2i.mm"
include "anbi1i.mm"
include "exbii.mm"
include "rabbii.mm"
include "inteqi.mm"
include "syl6eq.mm"
include "3eqtr3a.mm"

theorem relintab
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w

  disjoint ph w
  disjoint w x
  assert |- ( Rel |^| { x | ph } -> |^| { x | ph } = |^| { w e. ~P ( _V X. _V ) | E. x ( w = `' `' x /\ ph ) } )

  proof
    wph
    vx
    cab
    cint
    #
    wrel
    #
    @0
    ccnv
    ccnv
    #
    cvv
    cvv
    cxp
    #
    @0
    cin
    #
    @0
    vw
    cv
    #
    vx
    cv
    #
    ccnv
    ccnv
    #
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    vw
    @3
    cpw
    #
    crab
    #
    cint
    #
    @2
    @0
    @3
    cin
    @4
    @0
    cnvcnv
    @0
    @3
    incom
    eqtri
    @1
    @2
    @0
    wceq
    @0
    dfrel2
    biimpi
    @1
    @4
    @5
    @3
    @6
    cin
    #
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    vw
    @11
    crab
    #
    cint
    @13
    @1
    wph
    vx
    vw
    cvv
    cvv
    wph
    vx
    relintabex
    xpinintabd
    @18
    @12
    @17
    @10
    vw
    @11
    @16
    @9
    vx
    @15
    @8
    wph
    @14
    @7
    @5
    @14
    @6
    @3
    cin
    @7
    @3
    @6
    incom
    @6
    cnvcnv
    eqtr4i
    eqeq2i
    anbi1i
    exbii
    rabbii
    inteqi
    syl6eq
    3eqtr3a
end
