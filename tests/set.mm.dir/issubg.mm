include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "w3a.mm"
include "cdm.mm"
include "cv.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "df-subg.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "simp1.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rabeqbidv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "elrab.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "ibar.mm"
include "bitrd.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "pm5.21nii.mm"

theorem issubg
  let cB: class B
  let cS: class S
  let cG: class G
  let vs: setvar s
  let vw: setvar w
  assume issubg.b: |- B = ( Base ` G )


  assert |- ( S e. ( SubGrp ` G ) <-> ( G e. Grp /\ S C_ B /\ ( G |`s S ) e. Grp ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cG
    cgrp
    wcel
    #
    @2
    cS
    cB
    wss
    #
    cG
    cS
    cress
    co
    #
    cgrp
    wcel
    #
    w3a
    #
    @1
    csubg
    cdm
    cgrp
    cG
    vw
    cgrp
    vw
    cv
    #
    vs
    cv
    #
    cress
    co
    #
    cgrp
    wcel
    #
    vs
    @7
    cbs
    cfv
    #
    cpw
    #
    crab
    #
    csubg
    vw
    vs
    df-subg
    #
    dmmptss
    cS
    cG
    csubg
    elfvdm
    sseldi
    @2
    @3
    @5
    simp1
    @2
    @1
    @2
    @3
    @5
    wa
    #
    wa
    #
    @6
    @2
    @1
    @15
    @16
    @2
    @1
    cS
    cG
    @8
    cress
    co
    #
    cgrp
    wcel
    #
    vs
    cB
    cpw
    #
    crab
    #
    wcel
    #
    @15
    @2
    @0
    @20
    cS
    vw
    cG
    @13
    @20
    cgrp
    csubg
    @7
    cG
    wceq
    #
    @10
    @18
    vs
    @12
    @19
    @22
    @11
    cB
    @22
    @11
    cG
    cbs
    cfv
    #
    cB
    @7
    cG
    cbs
    fveq2
    issubg.b
    syl6eqr
    pweqd
    @22
    @9
    @17
    cgrp
    @7
    cG
    @8
    cress
    oveq1
    eleq1d
    rabeqbidv
    @14
    @18
    vs
    @19
    cB
    cB
    @23
    cvv
    issubg.b
    cG
    cbs
    fvex
    eqeltri
    #
    pwex
    rabex
    fvmpt
    eleq2d
    @21
    cS
    @19
    wcel
    #
    @5
    wa
    @15
    @18
    @5
    vs
    cS
    @19
    @8
    cS
    wceq
    @17
    @4
    cgrp
    @8
    cS
    cG
    cress
    oveq2
    eleq1d
    elrab
    @25
    @3
    @5
    cS
    cB
    @24
    elpw2
    anbi1i
    bitri
    syl6bb
    @2
    @15
    ibar
    bitrd
    @2
    @3
    @5
    3anass
    syl6bbr
    pm5.21nii
end
