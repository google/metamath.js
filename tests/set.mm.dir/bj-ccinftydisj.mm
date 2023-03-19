include "cc.mm"
include "cccinfty.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "wex.mm"
include "bj-inftyexpidisj.mm"
include "nex.mm"
include "wceq.mm"
include "wa.mm"
include "elin.mm"
include "crn.mm"
include "cdm.mm"
include "wrex.mm"
include "wfun.mm"
include "wi.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cop.mm"
include "df-bj-inftyexpi.mm"
include "funmpt2.mm"
include "elrnrexdm.mm"
include "ax-mp.mm"
include "rexex.mm"
include "syl.mm"
include "df-bj-ccinfty.mm"
include "eleq2s.mm"
include "anim2i.mm"
include "sylbi.mm"
include "ancom.mm"
include "exancom.mm"
include "19.41v.mm"
include "bitri.mm"
include "sylbb2.mm"
include "eleq1.mm"
include "biimpac.mm"
include "eximi.mm"
include "mto.mm"
include "nel0.mm"

theorem bj-ccinftydisj
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( CC i^i CCinfty ) = (/)

  proof
    vx
    cc
    cccinfty
    cin
    #
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    #
    cinftyexpi
    cfv
    #
    cc
    wcel
    #
    vy
    wex
    #
    @5
    vy
    @3
    bj-inftyexpidisj
    nex
    @2
    @1
    cc
    wcel
    #
    @1
    @4
    wceq
    #
    wa
    #
    vy
    wex
    #
    @6
    @2
    @7
    @8
    vy
    wex
    #
    wa
    #
    @10
    @2
    @7
    @1
    cccinfty
    wcel
    #
    wa
    @12
    @1
    cc
    cccinfty
    elin
    @13
    @11
    @7
    @11
    @1
    cinftyexpi
    crn
    #
    cccinfty
    @1
    @14
    wcel
    #
    @8
    vy
    cinftyexpi
    cdm
    #
    wrex
    #
    @11
    cinftyexpi
    wfun
    @15
    @17
    wi
    vz
    cpi
    cneg
    cpi
    cioc
    co
    vz
    cv
    cc
    cop
    cinftyexpi
    vz
    df-bj-inftyexpi
    funmpt2
    vy
    cinftyexpi
    @1
    elrnrexdm
    ax-mp
    @8
    vy
    @16
    rexex
    syl
    df-bj-ccinfty
    eleq2s
    anim2i
    sylbi
    @12
    @11
    @7
    wa
    #
    @10
    @7
    @11
    ancom
    @10
    @8
    @7
    wa
    vy
    wex
    @18
    @7
    @8
    vy
    exancom
    @8
    @7
    vy
    19.41v
    bitri
    sylbb2
    syl
    @9
    @5
    vy
    @8
    @7
    @5
    @1
    @4
    cc
    eleq1
    biimpac
    eximi
    syl
    mto
    nel0
end
