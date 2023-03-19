include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "uvtxval.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "nbgrel.mm"
include "df-3an.mm"
include "bitri.mm"
include "prcom.mm"
include "sseq1i.mm"
include "rexbii.mm"
include "id.mm"
include "eldifi.mm"
include "anim12ci.mm"
include "eldifsni.mm"
include "adantl.mm"
include "jca.mm"
include "biantrurd.mm"
include "syl5rbb.mm"
include "syl5bb.mm"
include "ralbidva.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem isuvtx
  let vv: setvar v
  let ve: setvar e
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let vn: setvar n
  let cN: class N
  let cW: class W
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
  disjoint G n
  disjoint n v
  disjoint N n
  disjoint N v
  disjoint V n
  disjoint W e
  disjoint W k
  disjoint W v
  assert |- ( UnivVtx ` G ) = { v e. V | A. k e. ( V \ { v } ) E. e e. E { k , v } C_ e }

  proof
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
    @1
    csn
    #
    cdif
    #
    wral
    #
    vv
    cV
    crab
    @0
    @1
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
    @4
    wral
    #
    vv
    cV
    crab
    vv
    vk
    cG
    cV
    uvtxel.v
    uvtxval
    @5
    @10
    vv
    cV
    @1
    cV
    wcel
    #
    @2
    @9
    vk
    @4
    @2
    @0
    cV
    wcel
    #
    @11
    wa
    #
    @0
    @1
    wne
    #
    wa
    #
    @1
    @0
    cpr
    #
    @7
    wss
    #
    ve
    cE
    wrex
    #
    wa
    #
    @11
    @0
    @4
    wcel
    #
    wa
    #
    @9
    @2
    @13
    @14
    @18
    w3a
    @19
    ve
    cE
    cG
    @0
    cV
    @1
    uvtxel.v
    isuvtx.e
    nbgrel
    @13
    @14
    @18
    df-3an
    bitri
    @9
    @18
    @21
    @19
    @8
    @17
    ve
    cE
    @6
    @16
    @7
    @0
    @1
    prcom
    sseq1i
    rexbii
    @21
    @15
    @18
    @21
    @13
    @14
    @11
    @11
    @20
    @12
    @11
    id
    @0
    cV
    @3
    eldifi
    anim12ci
    @20
    @14
    @11
    @0
    cV
    @1
    eldifsni
    adantl
    jca
    biantrurd
    syl5rbb
    syl5bb
    ralbidva
    rabbiia
    eqtri
end
