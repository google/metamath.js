include "clf.mm"
include "wcel.mm"
include "ccnfn.mm"
include "chil.mm"
include "cfv.mm"
include "cabs.mm"
include "cnmf.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cin.mm"
include "elin.mm"
include "wi.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "wceq.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "0lnfn.mm"
include "0cnfn.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "mpbi.mm"
include "simpli.mm"
include "simpri.mm"
include "nmcfnlbi.mm"
include "dedth.mm"
include "imp.mm"
include "sylanbr.mm"
include "3impa.mm"

theorem nmcfnlb
  let cA: class A
  let cT: class T


  assert |- ( ( T e. LinFn /\ T e. ContFn /\ A e. ~H ) -> ( abs ` ( T ` A ) ) <_ ( ( normfn ` T ) x. ( normh ` A ) ) )

  proof
    cT
    clf
    wcel
    #
    cT
    ccnfn
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cabs
    cfv
    #
    cT
    cnmf
    cfv
    #
    cA
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    wa
    cT
    clf
    ccnfn
    cin
    #
    wcel
    #
    @2
    @8
    cT
    clf
    ccnfn
    elin
    @10
    @2
    @8
    @10
    @2
    @8
    wi
    @2
    cA
    @10
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
    cabs
    cfv
    #
    @12
    cnmf
    cfv
    #
    @6
    cmul
    co
    #
    cle
    wbr
    #
    wi
    cT
    @11
    cT
    @12
    wceq
    #
    @8
    @17
    @2
    @18
    @4
    @14
    @7
    @16
    cle
    @18
    @3
    @13
    cabs
    cA
    cT
    @12
    fveq1
    fveq2d
    @18
    @5
    @15
    @6
    cmul
    cT
    @12
    cnmf
    fveq2
    oveq1d
    breq12d
    imbi2d
    cA
    @12
    @12
    clf
    wcel
    #
    @12
    ccnfn
    wcel
    #
    @12
    @9
    wcel
    @19
    @20
    wa
    cT
    @11
    @9
    @11
    @9
    wcel
    @11
    clf
    wcel
    @11
    ccnfn
    wcel
    0lnfn
    0cnfn
    @11
    clf
    ccnfn
    elin
    mpbir2an
    elimel
    @12
    clf
    ccnfn
    elin
    mpbi
    #
    simpli
    @19
    @20
    @21
    simpri
    nmcfnlbi
    dedth
    imp
    sylanbr
    3impa
end
