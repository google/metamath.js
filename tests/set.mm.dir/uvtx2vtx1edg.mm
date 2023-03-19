include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cuvtx.mm"
include "wral.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "nbgr2vtx1edg.mm"
include "wb.mm"
include "uvtxel.mm"
include "a1i.mm"
include "baibd.mm"
include "ralbidva.mm"
include "mpbird.mm"

theorem uvtx2vtx1edg
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
  assert |- ( ( ( # ` V ) = 2 /\ V e. E ) -> A. v e. V v e. ( UnivVtx ` G ) )

  proof
    cV
    chash
    cfv
    c2
    wceq
    cV
    cE
    wcel
    wa
    #
    vv
    cv
    #
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    wral
    vn
    cv
    cG
    @1
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
    vv
    vn
    cE
    cG
    cV
    uvtxel.v
    isuvtx.e
    nbgr2vtx1edg
    @0
    @2
    @3
    vv
    cV
    @0
    @2
    @1
    cV
    wcel
    #
    @3
    @2
    @4
    @3
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
    ralbidva
    mpbird
end
