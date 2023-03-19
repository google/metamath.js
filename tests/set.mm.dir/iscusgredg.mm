include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "iscusgr.mm"
include "cnbgr.mm"
include "co.mm"
include "iscplgrnb.mm"
include "nbusgreledg.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iscusgredg
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume iscusgrvtx.v: |- V = ( Vtx ` G )
  assume iscusgredg.v: |- E = ( Edg ` G )

  disjoint G k
  disjoint G n
  disjoint k n
  disjoint V k
  disjoint V n
  disjoint G v
  disjoint V v
  assert |- ( G e. ComplUSGraph <-> ( G e. USGraph /\ A. k e. V A. n e. ( V \ { k } ) { n , k } e. E ) )

  proof
    cG
    ccusgr
    wcel
    cG
    cusgr
    wcel
    #
    cG
    ccplgr
    wcel
    #
    wa
    @0
    vn
    cv
    #
    vk
    cv
    #
    cpr
    cE
    wcel
    #
    vn
    cV
    @3
    csn
    cdif
    #
    wral
    #
    vk
    cV
    wral
    #
    wa
    cG
    iscusgr
    @0
    @1
    @7
    @0
    @1
    @2
    cG
    @3
    cnbgr
    co
    wcel
    #
    vn
    @5
    wral
    #
    vk
    cV
    wral
    @7
    vk
    vn
    cG
    cV
    cusgr
    iscusgrvtx.v
    iscplgrnb
    @0
    @9
    @6
    vk
    cV
    @0
    @8
    @4
    vn
    @5
    cE
    cG
    @3
    @2
    iscusgredg.v
    nbusgreledg
    ralbidv
    ralbidv
    bitrd
    pm5.32i
    bitri
end
