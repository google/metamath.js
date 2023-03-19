include "com.mm"
include "wacn.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wral.mm"
include "wex.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "wb.mm"
include "vex.mm"
include "omex.mm"
include "isacn.mm"
include "mp2an.mm"
include "wfn.mm"
include "wne.mm"
include "wi.mm"
include "wa.mm"
include "axcc2.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "eldifsni.mm"
include "syl.mm"
include "sylan.mm"
include "id.mm"
include "syl5com.mm"
include "ralimdva.mm"
include "adantld.mm"
include "eximdv.mm"
include "mpi.mm"
include "mprgbir.mm"
include "2th.mm"
include "eqriv.mm"

theorem acncc
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- AC_ _om = _V

  proof
    vx
    com
    wacn
    #
    cvv
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cvv
    wcel
    #
    @2
    vy
    cv
    #
    vg
    cv
    #
    cfv
    @4
    vf
    cv
    #
    cfv
    #
    wcel
    #
    vy
    com
    wral
    #
    vg
    wex
    #
    vf
    @1
    cpw
    #
    c0
    csn
    cdif
    #
    com
    cmap
    co
    #
    @3
    com
    cvv
    wcel
    @2
    @10
    vf
    @13
    wral
    wb
    vx
    vex
    #
    omex
    vy
    com
    vf
    vg
    cvv
    cvv
    @1
    isacn
    mp2an
    @6
    @13
    wcel
    #
    @5
    com
    wfn
    #
    @7
    c0
    wne
    #
    @8
    wi
    #
    vy
    com
    wral
    #
    wa
    #
    vg
    wex
    @10
    vg
    vy
    @6
    axcc2
    @15
    @20
    @9
    vg
    @15
    @19
    @9
    @16
    @15
    @18
    @8
    vy
    com
    @15
    @4
    com
    wcel
    #
    wa
    @17
    @18
    @8
    @15
    com
    @12
    @6
    wf
    #
    @21
    @17
    @6
    @12
    com
    elmapi
    @22
    @21
    wa
    @7
    @12
    wcel
    @17
    com
    @12
    @4
    @6
    ffvelrn
    @7
    @11
    c0
    eldifsni
    syl
    sylan
    @18
    id
    syl5com
    ralimdva
    adantld
    eximdv
    mpi
    mprgbir
    @14
    2th
    eqriv
end
