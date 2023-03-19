include "clf.mm"
include "wcel.mm"
include "c0v.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "chil.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "0lnfn.mm"
include "elimel.mm"
include "lnfn0i.mm"
include "dedth.mm"

theorem lnfn0
  let cT: class T


  assert |- ( T e. LinFn -> ( T ` 0h ) = 0 )

  proof
    cT
    clf
    wcel
    #
    c0v
    cT
    cfv
    #
    cc0
    wceq
    c0v
    @0
    cT
    chil
    cc0
    csn
    cxp
    #
    cif
    #
    cfv
    #
    cc0
    wceq
    cT
    @2
    cT
    @3
    wceq
    @1
    @4
    cc0
    c0v
    cT
    @3
    fveq1
    eqeq1d
    @3
    cT
    @2
    clf
    0lnfn
    elimel
    lnfn0i
    dedth
end
