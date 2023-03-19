include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wss.mm"
include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "wrel.mm"
include "ccl.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "cxp.mm"
include "ciun.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "cnextfval.mm"
include "releqd.mm"
include "mpbiri.mm"

theorem cnextrel
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x
  assume cnextfrel.1: |- C = U. J
  assume cnextfrel.2: |- B = U. K


  assert |- ( ( ( J e. Top /\ K e. Top ) /\ ( F : A --> B /\ A C_ C ) ) -> Rel ( ( J CnExt K ) ` F ) )

  proof
    cJ
    ctop
    wcel
    cK
    ctop
    wcel
    wa
    cA
    cB
    cF
    wf
    cA
    cC
    wss
    wa
    wa
    #
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    wrel
    vx
    cA
    cJ
    ccl
    cfv
    cfv
    #
    vx
    cv
    csn
    #
    cF
    cK
    @3
    cJ
    cnei
    cfv
    cfv
    cA
    crest
    co
    cflf
    co
    cfv
    #
    cxp
    #
    ciun
    #
    wrel
    #
    @7
    @5
    wrel
    #
    vx
    @2
    wral
    @8
    vx
    @2
    @3
    @4
    relxp
    rgenw
    vx
    @2
    @5
    reliun
    mpbir
    @0
    @1
    @6
    vx
    cA
    cB
    cF
    cJ
    cK
    cC
    cnextfrel.1
    cnextfrel.2
    cnextfval
    releqd
    mpbiri
end
