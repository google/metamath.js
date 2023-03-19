include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cminusg.mm"
include "cnm.mm"
include "wceq.mm"
include "cnfldnm.mm"
include "a1i.mm"
include "cnfldneg.mm"
include "eqcomd.mm"
include "fveq12d.mm"
include "cngp.mm"
include "cnngp.mm"
include "cnfldbas.mm"
include "eqid.mm"
include "nminv.mm"
include "mpan.mm"
include "eqcomi.mm"
include "fveq1i.mm"
include "3eqtrd.mm"

theorem cnncvsabsnegdemo
  let cA: class A


  assert |- ( A e. CC -> ( abs ` -u A ) = ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    cabs
    cfv
    cA
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    ccnfld
    cnm
    cfv
    #
    cfv
    #
    cA
    @4
    cfv
    #
    cA
    cabs
    cfv
    #
    @0
    @1
    @3
    cabs
    @4
    cabs
    @4
    wceq
    @0
    cnfldnm
    a1i
    @0
    @3
    @1
    cA
    cnfldneg
    eqcomd
    fveq12d
    ccnfld
    cngp
    wcel
    @0
    @5
    @6
    wceq
    cnngp
    cA
    ccnfld
    @2
    @4
    cc
    cnfldbas
    @4
    eqid
    @2
    eqid
    nminv
    mpan
    @6
    @7
    wceq
    @0
    cA
    @4
    cabs
    cabs
    @4
    cnfldnm
    eqcomi
    fveq1i
    a1i
    3eqtrd
end
