include "wcel.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "crh.mm"
include "crab.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-rngiso.mm"
include "a1i.mm"
include "oveq12.mm"
include "adantl.mm"
include "ancoms.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "elex.mm"
include "adantr.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2d.mm"
include "cnveq.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isrim0
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s


  assert |- ( ( R e. V /\ S e. W ) -> ( F e. ( R RingIso S ) <-> ( F e. ( R RingHom S ) /\ `' F e. ( S RingHom R ) ) ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    wa
    #
    cF
    cR
    cS
    crs
    co
    #
    wcel
    cF
    vf
    cv
    #
    ccnv
    #
    cS
    cR
    crh
    co
    #
    wcel
    #
    vf
    cR
    cS
    crh
    co
    #
    crab
    #
    wcel
    cF
    @8
    wcel
    cF
    ccnv
    #
    @6
    wcel
    #
    wa
    @2
    @3
    @9
    cF
    @2
    vr
    vs
    cR
    cS
    cvv
    cvv
    @5
    vs
    cv
    #
    vr
    cv
    #
    crh
    co
    #
    wcel
    #
    vf
    @13
    @12
    crh
    co
    #
    crab
    #
    @9
    crs
    cvv
    crs
    vr
    vs
    cvv
    cvv
    @17
    cmpt2
    wceq
    @2
    vf
    vs
    vr
    df-rngiso
    a1i
    @2
    @13
    cR
    wceq
    #
    @12
    cS
    wceq
    #
    wa
    #
    wa
    #
    @15
    @7
    vf
    @16
    @8
    @20
    @16
    @8
    wceq
    @2
    @13
    cR
    @12
    cS
    crh
    oveq12
    adantl
    @21
    @14
    @6
    @5
    @20
    @14
    @6
    wceq
    #
    @2
    @19
    @18
    @22
    @12
    cS
    @13
    cR
    crh
    oveq12
    ancoms
    adantl
    eleq2d
    rabeqbidv
    @0
    cR
    cvv
    wcel
    @1
    cR
    cV
    elex
    adantr
    @1
    cS
    cvv
    wcel
    @0
    cS
    cW
    elex
    adantl
    @9
    cvv
    wcel
    @2
    @7
    vf
    @8
    cR
    cS
    crh
    ovex
    rabex
    a1i
    ovmpt2d
    eleq2d
    @7
    @11
    vf
    cF
    @8
    @4
    cF
    wceq
    @5
    @10
    @6
    @4
    cF
    cnveq
    eleq1d
    elrab
    syl6bb
end
