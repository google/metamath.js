include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "isuvtx.mm"
include "elrab2.mm"

theorem uvtxel1
  let ve: setvar e
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  let cW: class W
  assume uvtxel.v: |- V = ( Vtx ` G )
  assume isuvtx.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint G k
  disjoint e k
  disjoint V e
  disjoint V k
  disjoint N e
  disjoint N k
  disjoint G n
  disjoint G v
  disjoint n v
  disjoint N n
  disjoint N v
  disjoint V n
  disjoint V v
  disjoint e v
  disjoint k v
  disjoint W e
  disjoint W k
  disjoint W v
  disjoint E n
  disjoint e n
  disjoint k n
  assert |- ( N e. ( UnivVtx ` G ) <-> ( N e. V /\ A. k e. ( V \ { N } ) E. e e. E { k , N } C_ e ) )

  proof
    vk
    cv
    #
    vn
    cv
    #
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    vk
    cV
    @1
    csn
    #
    cdif
    #
    wral
    @0
    cN
    cpr
    #
    @3
    wss
    #
    ve
    cE
    wrex
    #
    vk
    cV
    cN
    csn
    #
    cdif
    #
    wral
    vn
    cN
    cV
    cG
    cuvtx
    cfv
    @1
    cN
    wceq
    #
    @5
    @10
    vk
    @7
    @12
    @13
    @6
    @11
    cV
    @1
    cN
    sneq
    difeq2d
    @13
    @4
    @9
    ve
    cE
    @13
    @2
    @8
    @3
    @1
    cN
    @0
    preq2
    sseq1d
    rexbidv
    raleqbidv
    vn
    ve
    vk
    cE
    cG
    cV
    uvtxel.v
    isuvtx.e
    isuvtx
    elrab2
end
