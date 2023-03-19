include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "co.mm"
include "cpv.mm"
include "cfv.mm"
include "cgi.mm"
include "c1st.mm"
include "cvc.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vc0.mm"
include "sylan.mm"
include "0vfval.mm"
include "adantr.mm"
include "eqtr4d.mm"

theorem nv0
  let cA: class A
  let cS: class S
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume nv0.1: |- X = ( BaseSet ` U )
  assume nv0.4: |- S = ( .sOLD ` U )
  assume nv0.6: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( 0 S A ) = Z )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cc0
    cA
    cS
    co
    #
    cU
    cpv
    cfv
    #
    cgi
    cfv
    #
    cZ
    @0
    cU
    c1st
    cfv
    #
    cvc
    wcel
    @1
    @2
    @4
    wceq
    cU
    @5
    @5
    eqid
    nvvc
    cA
    cS
    @3
    @5
    cX
    @4
    cU
    @3
    @3
    eqid
    #
    vafval
    cS
    cU
    nv0.4
    smfval
    cU
    @3
    cX
    nv0.1
    @6
    bafval
    @4
    eqid
    vc0
    sylan
    @0
    cZ
    @4
    wceq
    @1
    cU
    @3
    cnv
    cZ
    @6
    nv0.6
    0vfval
    adantr
    eqtr4d
end
