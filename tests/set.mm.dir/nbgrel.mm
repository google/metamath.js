include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "w3a.mm"
include "nbgrcl.mm"
include "pm4.71ri.mm"
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
include "bitri.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "anass.mm"
include "ancom.mm"
include "bitr3i.mm"
include "3bitr2ri.mm"

theorem nbgrel
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vn: setvar n
  let vv: setvar v
  assume nbgrel.v: |- V = ( Vtx ` G )
  assume nbgrel.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint X e
  disjoint V e
  disjoint e g
  disjoint e n
  disjoint e v
  disjoint g n
  disjoint g v
  disjoint n v
  disjoint G g
  disjoint X g
  disjoint E n
  disjoint G n
  disjoint N n
  disjoint X n
  disjoint V n
  assert |- ( N e. ( G NeighbVtx X ) <-> ( ( N e. V /\ X e. V ) /\ N =/= X /\ E. e e. E { X , N } C_ e ) )

  proof
    cN
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    cX
    cV
    wcel
    #
    @1
    wa
    #
    cN
    cV
    wcel
    #
    @2
    wa
    #
    cN
    cX
    wne
    #
    cX
    cN
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
    @1
    @2
    cG
    cN
    cV
    cX
    nbgrel.v
    nbgrcl
    pm4.71ri
    @3
    @2
    @4
    @6
    wa
    #
    @10
    wa
    #
    wa
    #
    @11
    @2
    @1
    @13
    @2
    @1
    cN
    cX
    vn
    cv
    #
    cpr
    #
    @8
    wss
    #
    ve
    cE
    wrex
    #
    vn
    cV
    cX
    csn
    cdif
    #
    crab
    #
    wcel
    #
    @13
    @2
    @0
    @20
    cN
    ve
    vn
    cE
    cG
    cX
    cV
    nbgrel.v
    nbgrel.e
    nbgrval
    eleq2d
    @21
    cN
    @19
    wcel
    #
    @10
    wa
    @13
    @18
    @10
    vn
    cN
    @19
    @15
    cN
    wceq
    #
    @17
    @9
    ve
    cE
    @23
    @16
    @7
    @8
    @15
    cN
    cX
    preq2
    sseq1d
    rexbidv
    elrab
    @22
    @12
    @10
    cN
    cV
    cX
    eldifsn
    anbi1i
    bitri
    syl6bb
    pm5.32i
    @11
    @5
    @6
    wa
    #
    @10
    wa
    @2
    @12
    wa
    #
    @10
    wa
    @14
    @5
    @6
    @10
    df-3an
    @25
    @24
    @10
    @25
    @2
    @4
    wa
    #
    @6
    wa
    @24
    @2
    @4
    @6
    anass
    @26
    @5
    @6
    @2
    @4
    ancom
    anbi1i
    bitr3i
    anbi1i
    @2
    @12
    @10
    anass
    3bitr2ri
    bitri
    bitri
end
