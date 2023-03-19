include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "w3a.mm"
include "wi.mm"
include "cvtx.mm"
include "cfv.mm"
include "nbgrclOLD.mm"
include "syl6eleqr.mm"
include "a1i.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "nbgrval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "preq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "eldifsn.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"
include "syl6bb.mm"
include "adantl.mm"
include "pm5.32da.mm"
include "3anass.mm"
include "ancom.mm"
include "3bitrri.mm"
include "bitrd.mm"

theorem nbgrelOLD
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume nbgrelOLD.v: |- V = ( Vtx ` G )
  assume nbgrelOLD.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint K e
  disjoint N e
  disjoint V e
  disjoint E k
  disjoint e k
  disjoint G k
  disjoint K k
  disjoint N k
  disjoint V k
  assert |- ( G e. W -> ( K e. ( G NeighbVtx N ) <-> ( ( K e. V /\ N e. V ) /\ K =/= N /\ E. e e. E { N , K } C_ e ) ) )

  proof
    cG
    cW
    wcel
    #
    cK
    cG
    cN
    cnbgr
    co
    #
    wcel
    #
    cN
    cV
    wcel
    #
    @2
    wa
    #
    cK
    cV
    wcel
    #
    @3
    wa
    #
    cK
    cN
    wne
    #
    cN
    cK
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
    @2
    @3
    @2
    @3
    wi
    @0
    @2
    cN
    cG
    cvtx
    cfv
    cV
    cG
    cK
    cN
    nbgrclOLD
    nbgrelOLD.v
    syl6eleqr
    a1i
    pm4.71rd
    @0
    @4
    @3
    @5
    @7
    @11
    wa
    #
    wa
    #
    wa
    #
    @12
    @0
    @3
    @2
    @14
    @3
    @2
    @14
    wb
    @0
    @3
    @2
    cK
    cN
    vk
    cv
    #
    cpr
    #
    @9
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
    cdif
    #
    crab
    #
    wcel
    #
    @14
    @3
    @1
    @21
    cK
    ve
    vk
    cE
    cG
    cN
    cV
    nbgrelOLD.v
    nbgrelOLD.e
    nbgrval
    eleq2d
    @22
    cK
    @20
    wcel
    #
    @11
    wa
    @5
    @7
    wa
    #
    @11
    wa
    @14
    @19
    @11
    vk
    cK
    @20
    @16
    cK
    wceq
    #
    @18
    @10
    ve
    cE
    @25
    @17
    @8
    @9
    @16
    cK
    cN
    preq2
    sseq1d
    rexbidv
    elrab
    @23
    @24
    @11
    cK
    cV
    cN
    eldifsn
    anbi1i
    @5
    @7
    @11
    anass
    3bitri
    syl6bb
    adantl
    pm5.32da
    @12
    @6
    @13
    wa
    @3
    @5
    wa
    #
    @13
    wa
    @15
    @6
    @7
    @11
    3anass
    @6
    @26
    @13
    @5
    @3
    ancom
    anbi1i
    @3
    @5
    @13
    anass
    3bitrri
    syl6bb
    bitrd
end
