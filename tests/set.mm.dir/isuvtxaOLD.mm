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
include "wss.mm"
include "wrex.mm"
include "uvtxavalOLD.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "nbgrel.mm"
include "df-3an.mm"
include "prcom.mm"
include "sseq1i.mm"
include "rexbii.mm"
include "simpr.mm"
include "eldifi.mm"
include "anim12ci.mm"
include "eldifsni.mm"
include "adantl.mm"
include "jca.mm"
include "biantrurd.mm"
include "syl5rbb.mm"
include "syl5bb.mm"
include "ralbidva.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem isuvtxaOLD
  let vv: setvar v
  let ve: setvar e
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let vn: setvar n
  let cN: class N
  assume uvtxel.v: |- V = ( Vtx ` G )
  assume isuvtx.e: |- E = ( Edg ` G )

  disjoint G v
  disjoint V v
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
  disjoint G n
  disjoint n v
  disjoint N n
  disjoint N v
  disjoint V n
  assert |- ( G e. W -> ( UnivVtx ` G ) = { v e. V | A. k e. ( V \ { v } ) E. e e. E { k , v } C_ e } )

  proof
    cG
    cW
    wcel
    #
    cG
    cuvtx
    cfv
    vk
    cv
    #
    cG
    vv
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
    #
    cdif
    #
    wral
    #
    vv
    cV
    crab
    @1
    @2
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
    @5
    wral
    #
    vv
    cV
    crab
    vv
    vk
    cG
    cV
    cW
    uvtxel.v
    uvtxavalOLD
    @0
    @6
    @11
    vv
    cV
    @0
    @2
    cV
    wcel
    #
    wa
    #
    @3
    @10
    vk
    @5
    @3
    @1
    cV
    wcel
    #
    @12
    wa
    #
    @1
    @2
    wne
    #
    @2
    @1
    cpr
    #
    @8
    wss
    #
    ve
    cE
    wrex
    #
    w3a
    #
    @13
    @1
    @5
    wcel
    #
    wa
    #
    @10
    ve
    cE
    cG
    @1
    cV
    @2
    uvtxel.v
    isuvtx.e
    nbgrel
    @20
    @15
    @16
    wa
    #
    @19
    wa
    #
    @22
    @10
    @15
    @16
    @19
    df-3an
    @10
    @19
    @22
    @24
    @9
    @18
    ve
    cE
    @7
    @17
    @8
    @1
    @2
    prcom
    sseq1i
    rexbii
    @22
    @23
    @19
    @22
    @15
    @16
    @13
    @12
    @21
    @14
    @0
    @12
    simpr
    @1
    cV
    @4
    eldifi
    anim12ci
    @21
    @16
    @13
    @1
    cV
    @2
    eldifsni
    adantl
    jca
    biantrurd
    syl5rbb
    syl5bb
    syl5bb
    ralbidva
    rabbidva
    eqtrd
end
