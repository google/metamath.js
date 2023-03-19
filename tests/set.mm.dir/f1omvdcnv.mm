include "wf1o.mm"
include "cv.mm"
include "ccnv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "f1ocnvfvb.mm"
include "3anidm23.mm"
include "bicomd.mm"
include "necon3bid.mm"
include "rabbidva.mm"
include "wfn.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "fndifnfp.mm"
include "3syl.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem f1omvdcnv
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cG: class G


  assert |- ( F : A -1-1-onto-> A -> dom ( `' F \ _I ) = dom ( F \ _I ) )

  proof
    cA
    cA
    cF
    wf1o
    #
    vx
    cv
    #
    cF
    ccnv
    #
    cfv
    #
    @1
    wne
    #
    vx
    cA
    crab
    #
    @1
    cF
    cfv
    #
    @1
    wne
    #
    vx
    cA
    crab
    #
    @2
    cid
    cdif
    cdm
    #
    cF
    cid
    cdif
    cdm
    #
    @0
    @4
    @7
    vx
    cA
    @0
    @1
    cA
    wcel
    #
    wa
    #
    @3
    @1
    @6
    @1
    @12
    @6
    @1
    wceq
    #
    @3
    @1
    wceq
    #
    @0
    @11
    @13
    @14
    wb
    cA
    cA
    @1
    @1
    cF
    f1ocnvfvb
    3anidm23
    bicomd
    necon3bid
    rabbidva
    @0
    cA
    cA
    @2
    wf1o
    @2
    cA
    wfn
    @9
    @5
    wceq
    cA
    cA
    cF
    f1ocnv
    cA
    cA
    @2
    f1ofn
    vx
    cA
    @2
    fndifnfp
    3syl
    @0
    cF
    cA
    wfn
    @10
    @8
    wceq
    cA
    cA
    cF
    f1ofn
    vx
    cA
    cF
    fndifnfp
    syl
    3eqtr4d
end
