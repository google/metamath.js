include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "ctop.mm"
include "cldrcl.mm"
include "adantr.mm"
include "cldss.mm"
include "simpr.mm"
include "clsss.mm"
include "syl3anc.mm"
include "wceq.mm"
include "cldcls.mm"
include "sseqtrd.mm"

theorem clsss2
  let cC: class C
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( C e. ( Clsd ` J ) /\ S C_ C ) -> ( ( cls ` J ) ` S ) C_ C )

  proof
    cC
    cJ
    ccld
    cfv
    wcel
    #
    cS
    cC
    wss
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    cC
    @3
    cfv
    #
    cC
    @2
    cJ
    ctop
    wcel
    #
    cC
    cX
    wss
    #
    @1
    @4
    @5
    wss
    @0
    @6
    @1
    cC
    cJ
    cldrcl
    adantr
    @0
    @7
    @1
    cC
    cJ
    cX
    clscld.1
    cldss
    adantr
    @0
    @1
    simpr
    cC
    cS
    cJ
    cX
    clscld.1
    clsss
    syl3anc
    @0
    @5
    cC
    wceq
    @1
    cC
    cJ
    cldcls
    adantr
    sseqtrd
end
