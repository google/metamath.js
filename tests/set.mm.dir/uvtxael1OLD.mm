include "wcel.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "isuvtxaOLD.mm"
include "eleq2d.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem uvtxael1OLD
  let ve: setvar e
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vn: setvar n
  let vv: setvar v
  assume uvtxel.v: |- V = ( Vtx ` G )
  assume isuvtx.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint G k
  disjoint e k
  disjoint V e
  disjoint V k
  disjoint W e
  disjoint W k
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
  disjoint W v
  disjoint E n
  disjoint e n
  disjoint k n
  disjoint E v
  disjoint W n
  assert |- ( G e. W -> ( N e. ( UnivVtx ` G ) <-> ( N e. V /\ A. k e. ( V \ { N } ) E. e e. E { k , N } C_ e ) ) )

  proof
    cG
    cW
    wcel
    #
    cN
    cG
    cuvtx
    cfv
    #
    wcel
    cN
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
    @3
    csn
    #
    cdif
    #
    wral
    #
    vn
    cV
    crab
    #
    wcel
    cN
    cV
    wcel
    @2
    cN
    cpr
    #
    @5
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
    #
    wa
    @0
    @1
    @11
    cN
    vn
    ve
    vk
    cE
    cG
    cV
    cW
    uvtxel.v
    isuvtx.e
    isuvtxaOLD
    eleq2d
    @10
    @17
    vn
    cN
    cV
    @3
    cN
    wceq
    #
    @7
    @14
    vk
    @9
    @16
    @18
    @8
    @15
    cV
    @3
    cN
    sneq
    difeq2d
    @18
    @6
    @13
    ve
    cE
    @18
    @4
    @12
    @5
    @3
    cN
    @2
    preq2
    sseq1d
    rexbidv
    raleqbidv
    elrab
    syl6bb
end
