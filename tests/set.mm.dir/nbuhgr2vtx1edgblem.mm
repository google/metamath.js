include "cuhgr.mm"
include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "cnbgr.mm"
include "co.mm"
include "wa.mm"
include "wne.mm"
include "wss.mm"
include "wrex.mm"
include "w3a.mm"
include "nbgrel.mm"
include "wi.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edguhgr.mm"
include "sylan2b.mm"
include "wb.mm"
include "eqeq1i.mm"
include "pweq.mm"
include "eleq2d.mm"
include "selpw.mm"
include "syl6bb.mm"
include "sylbi.mm"
include "adantl.mm"
include "prcom.mm"
include "sseq1i.mm"
include "eqss.mm"
include "eleq1a.mm"
include "a1i.mm"
include "com13.mm"
include "sylbir.mm"
include "ex.mm"
include "ad2antlr.mm"
include "sylbid.mm"
include "mpid.mm"
include "impancom.mm"
include "com14.mm"
include "rexlimdv.mm"
include "3impia.mm"
include "com12.mm"
include "syl5bi.mm"

theorem nbuhgr2vtx1edgblem
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vn: setvar n
  let vv: setvar v
  assume nbgr2vtx1edg.v: |- V = ( Vtx ` G )
  assume nbgr2vtx1edg.e: |- E = ( Edg ` G )

  disjoint E a
  disjoint E b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint V a
  disjoint V b
  disjoint E e
  disjoint E n
  disjoint a e
  disjoint a n
  disjoint b e
  disjoint b n
  disjoint e n
  disjoint G e
  disjoint G n
  disjoint G v
  disjoint a v
  disjoint b v
  disjoint e v
  disjoint n v
  disjoint V e
  disjoint V n
  disjoint V v
  assert |- ( ( G e. UHGraph /\ V = { a , b } /\ a e. ( G NeighbVtx b ) ) -> { a , b } e. E )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    @1
    cG
    @2
    cnbgr
    co
    wcel
    #
    @3
    cE
    wcel
    #
    @5
    @1
    cV
    wcel
    @2
    cV
    wcel
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
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    w3a
    #
    @0
    @4
    wa
    #
    @6
    ve
    cE
    cG
    @1
    cV
    @2
    nbgr2vtx1edg.v
    nbgr2vtx1edg.e
    nbgrel
    @13
    @14
    @6
    @7
    @8
    @12
    @14
    @6
    wi
    #
    @7
    @8
    wa
    #
    @11
    @15
    ve
    cE
    @14
    @10
    cE
    wcel
    #
    @11
    @16
    @6
    @0
    @17
    @4
    @11
    @16
    @6
    wi
    #
    wi
    #
    @0
    @17
    wa
    #
    @4
    @10
    cG
    cvtx
    cfv
    #
    cpw
    #
    wcel
    #
    @19
    @17
    @0
    @10
    cG
    cedg
    cfv
    #
    wcel
    @23
    cE
    @24
    @10
    nbgr2vtx1edg.e
    eleq2i
    @10
    cG
    edguhgr
    sylan2b
    @20
    @4
    @23
    @19
    wi
    @20
    @4
    wa
    @23
    @10
    @3
    wss
    #
    @19
    @4
    @23
    @25
    wb
    #
    @20
    @4
    @21
    @3
    wceq
    #
    @26
    cV
    @21
    @3
    nbgr2vtx1edg.v
    eqeq1i
    @27
    @23
    @10
    @3
    cpw
    #
    wcel
    @25
    @27
    @22
    @28
    @10
    @21
    @3
    pweq
    eleq2d
    ve
    @3
    selpw
    syl6bb
    sylbi
    adantl
    @17
    @25
    @19
    wi
    @0
    @4
    @11
    @25
    @17
    @18
    @11
    @3
    @10
    wss
    #
    @25
    @17
    @18
    wi
    #
    wi
    @9
    @3
    @10
    @2
    @1
    prcom
    sseq1i
    @29
    @25
    @30
    @29
    @25
    wa
    @3
    @10
    wceq
    #
    @30
    @3
    @10
    eqss
    @16
    @17
    @31
    @6
    @17
    @31
    @6
    wi
    wi
    @16
    @10
    cE
    @3
    eleq1a
    a1i
    com13
    sylbir
    ex
    sylbi
    com13
    ad2antlr
    sylbid
    ex
    mpid
    impancom
    com14
    rexlimdv
    3impia
    com12
    syl5bi
    3impia
end
