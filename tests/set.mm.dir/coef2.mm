include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "wa.mm"
include "cn0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "coef.mm"
include "adantr.mm"
include "wss.mm"
include "wceq.mm"
include "simpr.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "feq3d.mm"
include "mpbid.mm"

theorem coef2
  let cA: class A
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let vz: setvar z
  assume dgrval.1: |- A = ( coeff ` F )


  assert |- ( ( F e. ( Poly ` S ) /\ 0 e. S ) -> A : NN0 --> S )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cc0
    cS
    wcel
    #
    wa
    #
    cn0
    cS
    cc0
    csn
    #
    cun
    #
    cA
    wf
    #
    cn0
    cS
    cA
    wf
    @0
    @5
    @1
    cA
    cS
    cF
    dgrval.1
    coef
    adantr
    @2
    @4
    cS
    cA
    cn0
    @2
    @3
    cS
    wss
    @4
    cS
    wceq
    @2
    cc0
    cS
    @0
    @1
    simpr
    snssd
    @3
    cS
    ssequn2
    sylib
    feq3d
    mpbid
end
