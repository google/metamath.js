include "cumgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wne.mm"
include "cupgr.mm"
include "umgrupgr.mm"
include "eqid.mm"
include "upgrwlkvtxedg.mm"
include "sylan.mm"
include "wi.mm"
include "umgredgne.mm"
include "ex.mm"
include "adantr.mm"
include "ralimdv.mm"
include "mpd.mm"

theorem umgrwlknloop
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G

  disjoint F k
  disjoint G k
  disjoint P k
  assert |- ( ( G e. UMGraph /\ F ( Walks ` G ) P ) -> A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) =/= ( P ` ( k + 1 ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    wa
    #
    vk
    cv
    #
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    cP
    cfv
    #
    cpr
    cG
    cedg
    cfv
    #
    wcel
    #
    vk
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    #
    @4
    @5
    wne
    #
    vk
    @8
    wral
    @0
    cG
    cupgr
    wcel
    @1
    @9
    cG
    umgrupgr
    cP
    vk
    @6
    cF
    cG
    @6
    eqid
    #
    upgrwlkvtxedg
    sylan
    @2
    @7
    @10
    vk
    @8
    @0
    @7
    @10
    wi
    @1
    @0
    @7
    @10
    @6
    cG
    @4
    @5
    @11
    umgredgne
    ex
    adantr
    ralimdv
    mpd
end
