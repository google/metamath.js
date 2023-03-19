include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cuvtx.mm"
include "nbuhgr2vtx1edgb.mm"
include "wb.mm"
include "uvtxel.mm"
include "a1i.mm"
include "baibd.mm"
include "bicomd.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem uvtx2vtx1edgb
  let vv: setvar v
  let cE: class E
  let cG: class G
  let cV: class V
  let vn: setvar n
  let cN: class N
  let ve: setvar e
  let vk: setvar k
  let cW: class W
  assume uvtxel.v: |- V = ( Vtx ` G )
  assume isuvtx.e: |- E = ( Edg ` G )

  disjoint G v
  disjoint V v
  disjoint E v
  disjoint G n
  disjoint n v
  disjoint N n
  disjoint N v
  disjoint V n
  disjoint E e
  disjoint G e
  disjoint G k
  disjoint e k
  disjoint e v
  disjoint k v
  disjoint V e
  disjoint V k
  disjoint W e
  disjoint W k
  disjoint W v
  disjoint E n
  disjoint N e
  disjoint N k
  disjoint e n
  disjoint k n
  disjoint W n
  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 2 ) -> ( V e. E <-> A. v e. V v e. ( UnivVtx ` G ) ) )

  proof
    cG
    cuhgr
    wcel
    cV
    chash
    cfv
    c2
    wceq
    wa
    #
    cV
    cE
    wcel
    vn
    cv
    cG
    vv
    cv
    #
    cnbgr
    co
    wcel
    vn
    cV
    @1
    csn
    cdif
    wral
    #
    vv
    cV
    wral
    @1
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    wral
    vv
    vn
    cE
    cG
    cV
    uvtxel.v
    isuvtx.e
    nbuhgr2vtx1edgb
    @0
    @2
    @3
    vv
    cV
    @0
    @1
    cV
    wcel
    #
    wa
    @3
    @2
    @0
    @3
    @4
    @2
    @3
    @4
    @2
    wa
    wb
    @0
    vn
    cG
    @1
    cV
    uvtxel.v
    uvtxel
    a1i
    baibd
    bicomd
    ralbidva
    bitrd
end
