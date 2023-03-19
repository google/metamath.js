include "wcel.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "bastg.mm"
include "adantr.mm"
include "sstr2.mm"
include "syl.mm"
include "cvv.mm"
include "fvex.mm"
include "tgss.mm"
include "mpan.mm"
include "wceq.mm"
include "tgidm.mm"
include "adantl.mm"
include "sseq2d.mm"
include "syl5ib.mm"
include "impbid.mm"

theorem tgss3
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J


  assert |- ( ( B e. V /\ C e. W ) -> ( ( topGen ` B ) C_ ( topGen ` C ) <-> B C_ ( topGen ` C ) ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    wa
    #
    cB
    ctg
    cfv
    #
    cC
    ctg
    cfv
    #
    wss
    #
    cB
    @4
    wss
    #
    @2
    cB
    @3
    wss
    #
    @5
    @6
    wi
    @0
    @7
    @1
    cB
    cV
    bastg
    adantr
    cB
    @3
    @4
    sstr2
    syl
    @6
    @3
    @4
    ctg
    cfv
    #
    wss
    #
    @2
    @5
    @4
    cvv
    wcel
    @6
    @9
    cC
    ctg
    fvex
    cB
    @4
    cvv
    tgss
    mpan
    @2
    @8
    @4
    @3
    @1
    @8
    @4
    wceq
    @0
    cC
    cW
    tgidm
    adantl
    sseq2d
    syl5ib
    impbid
end
