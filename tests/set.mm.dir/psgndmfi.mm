include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "wfn.mm"
include "csymg.mm"
include "cfv.mm"
include "eqid.mm"
include "psgnfn.mm"
include "wral.mm"
include "wceq.mm"
include "sygbasnfpfi.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqcomd.mm"
include "fneq2d.mm"
include "mpbii.mm"

theorem psgndmfi
  let cD: class D
  let cS: class S
  let cG: class G
  let vp: setvar p
  assume psgndmfi.s: |- S = ( pmSgn ` D )
  assume psgndmfi.g: |- G = ( Base ` ( SymGrp ` D ) )


  assert |- ( D e. Fin -> S Fn G )

  proof
    cD
    cfn
    wcel
    #
    cS
    vp
    cv
    #
    cid
    cdif
    cdm
    cfn
    wcel
    #
    vp
    cG
    crab
    #
    wfn
    cS
    cG
    wfn
    cG
    cD
    @3
    cD
    csymg
    cfv
    #
    cS
    vp
    @4
    eqid
    #
    psgndmfi.g
    @3
    eqid
    psgndmfi.s
    psgnfn
    @0
    @3
    cG
    cS
    @0
    cG
    @3
    @0
    @2
    vp
    cG
    wral
    cG
    @3
    wceq
    @0
    @2
    vp
    cG
    cG
    cD
    @1
    @4
    @5
    psgndmfi.g
    sygbasnfpfi
    ralrimiva
    @2
    vp
    cG
    rabid2
    sylibr
    eqcomd
    fneq2d
    mpbii
end
