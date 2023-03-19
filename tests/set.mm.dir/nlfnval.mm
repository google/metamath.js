include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cnl.mm"
include "cfv.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "cnex.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "cvv.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "syl.mm"
include "cv.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "df-nlfn.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "sylbir.mm"

theorem nlfnval
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> CC -> ( null ` T ) = ( `' T " { 0 } ) )

  proof
    chil
    cc
    cT
    wf
    cT
    cc
    chil
    cmap
    co
    #
    wcel
    #
    cT
    cnl
    cfv
    cT
    ccnv
    #
    cc0
    csn
    #
    cima
    #
    wceq
    #
    cc
    chil
    cT
    cnex
    ax-hilex
    elmap
    @1
    @4
    cvv
    wcel
    #
    @5
    @1
    @2
    cvv
    wcel
    @6
    cT
    @0
    cnvexg
    @2
    @3
    cvv
    imaexg
    syl
    vt
    cT
    vt
    cv
    #
    ccnv
    #
    @3
    cima
    @4
    @0
    cvv
    cnl
    @7
    cT
    wceq
    @8
    @2
    @3
    @7
    cT
    cnveq
    imaeq1d
    vt
    df-nlfn
    fvmptg
    mpdan
    sylbir
end
