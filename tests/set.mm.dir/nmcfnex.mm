include "clf.mm"
include "wcel.mm"
include "ccnfn.mm"
include "wa.mm"
include "cin.mm"
include "cnmf.mm"
include "cfv.mm"
include "cr.mm"
include "elin.mm"
include "chil.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "0lnfn.mm"
include "0cnfn.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "mpbi.mm"
include "simpli.mm"
include "simpri.mm"
include "nmcfnexi.mm"
include "dedth.mm"
include "sylbir.mm"

theorem nmcfnex
  let cT: class T


  assert |- ( ( T e. LinFn /\ T e. ContFn ) -> ( normfn ` T ) e. RR )

  proof
    cT
    clf
    wcel
    cT
    ccnfn
    wcel
    wa
    cT
    clf
    ccnfn
    cin
    #
    wcel
    #
    cT
    cnmf
    cfv
    #
    cr
    wcel
    #
    cT
    clf
    ccnfn
    elin
    @1
    @3
    @1
    cT
    chil
    cc0
    csn
    cxp
    #
    cif
    #
    cnmf
    cfv
    #
    cr
    wcel
    cT
    @4
    cT
    @5
    wceq
    @2
    @6
    cr
    cT
    @5
    cnmf
    fveq2
    eleq1d
    @5
    @5
    clf
    wcel
    #
    @5
    ccnfn
    wcel
    #
    @5
    @0
    wcel
    @7
    @8
    wa
    cT
    @4
    @0
    @4
    @0
    wcel
    @4
    clf
    wcel
    @4
    ccnfn
    wcel
    0lnfn
    0cnfn
    @4
    clf
    ccnfn
    elin
    mpbir2an
    elimel
    @5
    clf
    ccnfn
    elin
    mpbi
    #
    simpli
    @7
    @8
    @9
    simpri
    nmcfnexi
    dedth
    sylbir
end
