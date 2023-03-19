include "cimage.mm"
include "cvv.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "wfun.mm"
include "wrel.mm"
include "funimage.mm"
include "funrel.mm"
include "ax-mp.mm"
include "mptrel.mm"
include "wbr.mm"
include "wcel.mm"
include "cab.mm"
include "cdm.mm"
include "vex.mm"
include "breldm.mm"
include "wfn.mm"
include "wceq.mm"
include "fnimage.mm"
include "fndm.mm"
include "syl6eleq.mm"
include "crab.mm"
include "eqid.mm"
include "dmmpt.mm"
include "rabab.mm"
include "eqtri.mm"
include "wb.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elab.mm"
include "brimage.mm"
include "eqcom.mm"
include "cfv.mm"
include "fvmptg.mm"
include "mpan.mm"
include "eqeq1d.mm"
include "funmpt.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "biimpri.mm"
include "fnbrfvb.mm"
include "sylancr.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "sylbi.mm"
include "pm5.21nii.mm"
include "eqbrriv.mm"

theorem imageval
  let vx: setvar x
  let cR: class R
  let vy: setvar y
  let vz: setvar z

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- Image R = ( x e. _V |-> ( R " x ) )

  proof
    vy
    vz
    cR
    cimage
    #
    vx
    cvv
    cR
    vx
    cv
    #
    cima
    #
    cmpt
    #
    @0
    wfun
    @0
    wrel
    cR
    funimage
    @0
    funrel
    ax-mp
    vx
    cvv
    @2
    mptrel
    vy
    cv
    #
    vz
    cv
    #
    @0
    wbr
    #
    @4
    @2
    cvv
    wcel
    #
    vx
    cab
    #
    wcel
    #
    @4
    @5
    @3
    wbr
    #
    @6
    @4
    @0
    cdm
    #
    @8
    @4
    @5
    @0
    vy
    vex
    #
    vz
    vex
    #
    breldm
    @0
    @8
    wfn
    @11
    @8
    wceq
    vx
    cR
    fnimage
    @8
    @0
    fndm
    ax-mp
    syl6eleq
    @10
    @4
    @3
    cdm
    #
    @8
    @4
    @5
    @3
    @12
    @13
    breldm
    @14
    @7
    vx
    cvv
    crab
    @8
    vx
    cvv
    @2
    @3
    @3
    eqid
    #
    dmmpt
    @7
    vx
    rabab
    eqtri
    #
    syl6eleq
    @9
    cR
    @4
    cima
    #
    cvv
    wcel
    #
    @6
    @10
    wb
    @7
    @18
    vx
    @4
    @12
    @1
    @4
    wceq
    @2
    @17
    cvv
    @1
    @4
    cR
    imaeq2
    #
    eleq1d
    elab
    #
    @6
    @5
    @17
    wceq
    #
    @18
    @10
    @4
    @5
    cR
    @12
    @13
    brimage
    @21
    @17
    @5
    wceq
    #
    @18
    @10
    @5
    @17
    eqcom
    @18
    @4
    @3
    cfv
    #
    @5
    wceq
    #
    @22
    @10
    @18
    @23
    @17
    @5
    @4
    cvv
    wcel
    @18
    @23
    @17
    wceq
    @12
    vx
    @4
    @2
    @17
    cvv
    cvv
    @3
    @19
    @15
    fvmptg
    mpan
    eqeq1d
    @18
    @3
    @8
    wfn
    #
    @9
    @24
    @10
    wb
    @25
    @3
    wfun
    @14
    @8
    wceq
    vx
    cvv
    @2
    funmpt
    @16
    @3
    @8
    df-fn
    mpbir2an
    @9
    @18
    @20
    biimpri
    @8
    @4
    @5
    @3
    fnbrfvb
    sylancr
    bitr3d
    syl5bb
    syl5bb
    sylbi
    pm5.21nii
    eqbrriv
end
