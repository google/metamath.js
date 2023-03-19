include "cz.mm"
include "wcel.mm"
include "csn.mm"
include "clcmf.mm"
include "cfv.mm"
include "cpr.mm"
include "clcm.mm"
include "co.mm"
include "cabs.mm"
include "wceq.mm"
include "dfsn2.mm"
include "a1i.mm"
include "fveq2d.mm"
include "lcmfpr.mm"
include "anidms.mm"
include "lcmid.mm"
include "3eqtrd.mm"

theorem lcmfsn
  let cM: class M


  assert |- ( M e. ZZ -> ( _lcm ` { M } ) = ( abs ` M ) )

  proof
    cM
    cz
    wcel
    #
    cM
    csn
    #
    clcmf
    cfv
    cM
    cM
    cpr
    #
    clcmf
    cfv
    #
    cM
    cM
    clcm
    co
    #
    cM
    cabs
    cfv
    @0
    @1
    @2
    clcmf
    @1
    @2
    wceq
    @0
    cM
    dfsn2
    a1i
    fveq2d
    @0
    @3
    @4
    wceq
    cM
    cM
    lcmfpr
    anidms
    cM
    lcmid
    3eqtrd
end
