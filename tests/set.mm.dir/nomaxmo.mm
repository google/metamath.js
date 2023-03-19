include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "ccnv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrmo.mm"
include "wor.mm"
include "sltso.mm"
include "soss.mm"
include "mpi.mm"
include "cnvso.mm"
include "sylib.mm"
include "somo.mm"
include "syl.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "rmobii.mm"

theorem nomaxmo
  let vx: setvar x
  let vy: setvar y
  let cS: class S

  disjoint S x
  disjoint S y
  disjoint x y
  assert |- ( S C_ No -> E* x e. S A. y e. S -. x <s y )

  proof
    cS
    csur
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    cslt
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    cS
    wral
    #
    vx
    cS
    wrmo
    #
    @2
    @1
    cslt
    wbr
    #
    wn
    #
    vy
    cS
    wral
    #
    vx
    cS
    wrmo
    @0
    cS
    @3
    wor
    #
    @7
    @0
    cS
    cslt
    wor
    #
    @11
    @0
    csur
    cslt
    wor
    @12
    sltso
    cS
    csur
    cslt
    soss
    mpi
    cS
    cslt
    cnvso
    sylib
    vx
    vy
    cS
    @3
    somo
    syl
    @6
    @10
    vx
    cS
    @5
    @9
    vy
    cS
    @4
    @8
    @1
    @2
    cslt
    vy
    vex
    vx
    vex
    brcnv
    notbii
    ralbii
    rmobii
    sylib
end
