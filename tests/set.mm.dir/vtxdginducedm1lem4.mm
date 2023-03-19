include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "c0.mm"
include "chash.mm"
include "cc0.mm"
include "wn.mm"
include "wral.mm"
include "cdm.mm"
include "wi.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "elrab2.mm"
include "wne.mm"
include "eldifsn.mm"
include "df-ne.mm"
include "eleq2.mm"
include "elsni.mm"
include "eqcomd.mm"
include "syl6bi.mm"
include "com12.mm"
include "con3rr3.mm"
include "sylbi.mm"
include "simplbiim.mm"
include "impcom.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "cvv.mm"
include "wb.mm"
include "ciedg.mm"
include "fvexi.mm"
include "dmex.mm"
include "rabex.mm"
include "eqeltri.mm"
include "hasheq0.mm"
include "ax-mp.mm"

theorem vtxdginducedm1lem4
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume vtxdginducedm1.v: |- V = ( Vtx ` G )
  assume vtxdginducedm1.e: |- E = ( iEdg ` G )
  assume vtxdginducedm1.k: |- K = ( V \ { N } )
  assume vtxdginducedm1.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume vtxdginducedm1.p: |- P = ( E |` I )
  assume vtxdginducedm1.s: |- S = <. K , P >.
  assume vtxdginducedm1.j: |- J = { i e. dom E | N e. ( E ` i ) }

  disjoint E i
  disjoint J k
  disjoint N i
  disjoint N k
  disjoint i k
  disjoint V k
  disjoint W k
  assert |- ( W e. ( V \ { N } ) -> ( # ` { k e. J | ( E ` k ) = { W } } ) = 0 )

  proof
    cW
    cV
    cN
    csn
    cdif
    wcel
    #
    vk
    cv
    #
    cE
    cfv
    #
    cW
    csn
    #
    wceq
    #
    vk
    cJ
    crab
    #
    c0
    wceq
    #
    @5
    chash
    cfv
    cc0
    wceq
    #
    @0
    @4
    wn
    #
    vk
    cJ
    wral
    @6
    @0
    @8
    vk
    cJ
    @1
    cJ
    wcel
    #
    @0
    @8
    @9
    @1
    cE
    cdm
    #
    wcel
    cN
    @2
    wcel
    #
    @0
    @8
    wi
    cN
    vi
    cv
    #
    cE
    cfv
    #
    wcel
    #
    @11
    vi
    @1
    @10
    cJ
    vi
    vk
    weq
    @13
    @2
    cN
    @12
    @1
    cE
    fveq2
    eleq2d
    vtxdginducedm1.j
    elrab2
    @0
    @11
    @8
    @0
    cW
    cV
    wcel
    cW
    cN
    wne
    #
    @11
    @8
    wi
    #
    cW
    cV
    cN
    eldifsn
    @15
    cW
    cN
    wceq
    #
    wn
    @16
    cW
    cN
    df-ne
    @11
    @4
    @17
    @4
    @11
    @17
    @4
    @11
    cN
    @3
    wcel
    #
    @17
    @2
    @3
    cN
    eleq2
    @18
    cN
    cW
    cN
    cW
    elsni
    eqcomd
    syl6bi
    com12
    con3rr3
    sylbi
    simplbiim
    com12
    simplbiim
    impcom
    ralrimiva
    @4
    vk
    cJ
    rabeq0
    sylibr
    @5
    cvv
    wcel
    @7
    @6
    wb
    @4
    vk
    cJ
    cJ
    @14
    vi
    @10
    crab
    cvv
    vtxdginducedm1.j
    @14
    vi
    @10
    cE
    cE
    cG
    ciedg
    vtxdginducedm1.e
    fvexi
    dmex
    rabex
    eqeltri
    rabex
    @5
    cvv
    hasheq0
    ax-mp
    sylibr
end
