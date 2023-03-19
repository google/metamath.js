include "csdrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cdr.mm"
include "csubrg.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "w3a.mm"
include "cdm.mm"
include "cv.mm"
include "crab.mm"
include "df-sdrg.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rabeqbidv.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biadan2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem issdrg
  let cR: class R
  let cS: class S
  let vs: setvar s
  let vw: setvar w


  assert |- ( S e. ( SubDRing ` R ) <-> ( R e. DivRing /\ S e. ( SubRing ` R ) /\ ( R |`s S ) e. DivRing ) )

  proof
    cS
    cR
    csdrg
    cfv
    #
    wcel
    #
    cR
    cdr
    wcel
    #
    cS
    cR
    csubrg
    cfv
    #
    wcel
    #
    cR
    cS
    cress
    co
    #
    cdr
    wcel
    #
    wa
    #
    wa
    @2
    @4
    @6
    w3a
    @1
    @2
    @7
    @1
    csdrg
    cdm
    cdr
    cR
    vw
    cdr
    vw
    cv
    #
    vs
    cv
    #
    cress
    co
    #
    cdr
    wcel
    #
    vs
    @8
    csubrg
    cfv
    #
    crab
    #
    csdrg
    vw
    vs
    df-sdrg
    #
    dmmptss
    cS
    cR
    csdrg
    elfvdm
    sseldi
    @2
    @1
    cS
    cR
    @9
    cress
    co
    #
    cdr
    wcel
    #
    vs
    @3
    crab
    #
    wcel
    @7
    @2
    @0
    @17
    cS
    vw
    cR
    @13
    @17
    cdr
    csdrg
    @8
    cR
    wceq
    #
    @11
    @16
    vs
    @12
    @3
    @8
    cR
    csubrg
    fveq2
    @18
    @10
    @15
    cdr
    @8
    cR
    @9
    cress
    oveq1
    eleq1d
    rabeqbidv
    @14
    @16
    vs
    @3
    cR
    csubrg
    fvex
    rabex
    fvmpt
    eleq2d
    @16
    @6
    vs
    cS
    @3
    @9
    cS
    wceq
    @15
    @5
    cdr
    @9
    cS
    cR
    cress
    oveq2
    eleq1d
    elrab
    syl6bb
    biadan2
    @2
    @4
    @6
    3anass
    bitr4i
end
