include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wreu.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "reubidv.mm"
include "inss1.mm"
include "0lnfn.mm"
include "0cnfn.mm"
include "elin.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "sselii.mm"
include "inss2.mm"
include "riesz4i.mm"
include "dedth.mm"

theorem riesz4
  let vw: setvar w
  let vv: setvar v
  let cT: class T

  disjoint v w
  disjoint T w
  disjoint T v
  assert |- ( T e. ( LinFn i^i ContFn ) -> E! w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w ) )

  proof
    cT
    clf
    ccnfn
    cin
    #
    wcel
    #
    vv
    cv
    #
    cT
    cfv
    #
    @2
    vw
    cv
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    wreu
    @2
    @1
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
    @4
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    wreu
    cT
    @7
    cT
    @8
    wceq
    #
    @6
    @11
    vw
    chil
    @12
    @5
    @10
    vv
    chil
    @12
    @3
    @9
    @4
    @2
    cT
    @8
    fveq1
    eqeq1d
    ralbidv
    reubidv
    vw
    vv
    @8
    @0
    clf
    @8
    clf
    ccnfn
    inss1
    cT
    @7
    @0
    @7
    @0
    wcel
    @7
    clf
    wcel
    @7
    ccnfn
    wcel
    0lnfn
    0cnfn
    @7
    clf
    ccnfn
    elin
    mpbir2an
    elimel
    #
    sselii
    @0
    ccnfn
    @8
    clf
    ccnfn
    inss2
    @13
    sselii
    riesz4i
    dedth
end
