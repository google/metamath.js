include "cnv.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cpv.mm"
include "cfv.mm"
include "cgi.mm"
include "co.mm"
include "c1st.mm"
include "cvc.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "cba.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcz.mm"
include "sylan.mm"
include "0vfval.mm"
include "adantr.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem nvsz
  let cA: class A
  let cS: class S
  let cU: class U
  let cZ: class Z
  assume nvsz.4: |- S = ( .sOLD ` U )
  assume nvsz.6: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. CC ) -> ( A S Z ) = Z )

  proof
    cU
    cnv
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    #
    cA
    cU
    cpv
    cfv
    #
    cgi
    cfv
    #
    cS
    co
    #
    @4
    cA
    cZ
    cS
    co
    cZ
    @0
    cU
    c1st
    cfv
    #
    cvc
    wcel
    @1
    @5
    @4
    wceq
    cU
    @6
    @6
    eqid
    nvvc
    cA
    cS
    @3
    @6
    cU
    cba
    cfv
    #
    @4
    cU
    @3
    @3
    eqid
    #
    vafval
    cS
    cU
    nvsz.4
    smfval
    cU
    @3
    @7
    @7
    eqid
    @8
    bafval
    @4
    eqid
    vcz
    sylan
    @2
    cZ
    @4
    cA
    cS
    @0
    cZ
    @4
    wceq
    @1
    cU
    @3
    cnv
    cZ
    @8
    nvsz.6
    0vfval
    adantr
    #
    oveq2d
    @9
    3eqtr4d
end
