include "cusgr.mm"
include "wcel.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "cpr.mm"
include "uvtxval.mm"
include "nbusgreledg.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "syl5eq.mm"

theorem uvtxusgr
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cV: class V
  let cN: class N
  let vv: setvar v
  assume uvtxnbgr.v: |- V = ( Vtx ` G )
  assume uvtxusgr.e: |- E = ( Edg ` G )

  disjoint G n
  disjoint V n
  disjoint G k
  disjoint k n
  disjoint V k
  disjoint N n
  disjoint V v
  disjoint k v
  assert |- ( G e. USGraph -> ( UnivVtx ` G ) = { n e. V | A. k e. ( V \ { n } ) { k , n } e. E } )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cuvtx
    cfv
    vk
    cv
    #
    cG
    vn
    cv
    #
    cnbgr
    co
    wcel
    #
    vk
    cV
    @2
    csn
    cdif
    #
    wral
    #
    vn
    cV
    crab
    @1
    @2
    cpr
    cE
    wcel
    #
    vk
    @4
    wral
    #
    vn
    cV
    crab
    vn
    vk
    cG
    cV
    uvtxnbgr.v
    uvtxval
    @0
    @5
    @7
    vn
    cV
    @0
    @3
    @6
    vk
    @4
    cE
    cG
    @2
    @1
    uvtxusgr.e
    nbusgreledg
    ralbidv
    rabbidv
    syl5eq
end
