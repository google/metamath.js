include "cvv.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cdm.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "cae.mm"
include "copab.mm"
include "cfae.mm"
include "wceq.mm"
include "simpl.mm"
include "dmeqd.mm"
include "simpr.mm"
include "unieqd.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "breqd.mm"
include "rabeqbidv.mm"
include "breq12d.mm"
include "opabbidv.mm"
include "df-fae.mm"
include "cxp.mm"
include "ovex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "ovmpt2a.mm"

theorem faeval
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cM: class M
  let vm: setvar m
  let vr: setvar r

  disjoint f g
  disjoint f x
  disjoint M f
  disjoint g x
  disjoint M g
  disjoint M x
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint f m
  disjoint f r
  disjoint g m
  disjoint g r
  disjoint m r
  disjoint m x
  disjoint M m
  disjoint r x
  disjoint M r
  disjoint R m
  disjoint R r
  assert |- ( ( R e. _V /\ M e. U. ran measures ) -> ( R ~ae M ) = { <. f , g >. | ( ( f e. ( dom R ^m U. dom M ) /\ g e. ( dom R ^m U. dom M ) ) /\ { x e. U. dom M | ( f ` x ) R ( g ` x ) } ae M ) } )

  proof
    vr
    vm
    cR
    cM
    cvv
    cmeas
    crn
    cuni
    vf
    cv
    #
    vr
    cv
    #
    cdm
    #
    vm
    cv
    #
    cdm
    #
    cuni
    #
    cmap
    co
    #
    wcel
    #
    vg
    cv
    #
    @6
    wcel
    #
    wa
    #
    vx
    cv
    #
    @0
    cfv
    #
    @11
    @8
    cfv
    #
    @1
    wbr
    #
    vx
    @5
    crab
    #
    @3
    cae
    wbr
    #
    wa
    #
    vf
    vg
    copab
    @0
    cR
    cdm
    #
    cM
    cdm
    #
    cuni
    #
    cmap
    co
    #
    wcel
    #
    @8
    @21
    wcel
    #
    wa
    #
    @12
    @13
    cR
    wbr
    #
    vx
    @20
    crab
    #
    cM
    cae
    wbr
    #
    wa
    #
    vf
    vg
    copab
    #
    cfae
    @1
    cR
    wceq
    #
    @3
    cM
    wceq
    #
    wa
    #
    @17
    @28
    vf
    vg
    @32
    @10
    @24
    @16
    @27
    @32
    @7
    @22
    @9
    @23
    @32
    @6
    @21
    @0
    @32
    @2
    @18
    @5
    @20
    cmap
    @32
    @1
    cR
    @30
    @31
    simpl
    #
    dmeqd
    @32
    @4
    @19
    @32
    @3
    cM
    @30
    @31
    simpr
    #
    dmeqd
    unieqd
    #
    oveq12d
    #
    eleq2d
    @32
    @6
    @21
    @8
    @36
    eleq2d
    anbi12d
    @32
    @15
    @26
    @3
    cM
    cae
    @32
    @14
    @25
    vx
    @5
    @20
    @35
    @32
    @1
    cR
    @12
    @13
    @33
    breqd
    rabeqbidv
    @34
    breq12d
    anbi12d
    opabbidv
    vx
    vf
    vg
    vm
    vr
    df-fae
    @29
    @21
    @21
    cxp
    @21
    @21
    @18
    @20
    cmap
    ovex
    #
    @37
    xpex
    @27
    vf
    vg
    @21
    @21
    opabssxp
    ssexi
    ovmpt2a
end
