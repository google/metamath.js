include "cid.mm"
include "cv.mm"
include "wnel.mm"
include "cop.mm"
include "cedg.mm"
include "cfv.mm"
include "crab.mm"
include "cres.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfusgr.mm"
include "w3a.mm"
include "residfi.mm"
include "ciedg.mm"
include "wb.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "eqid.mm"
include "usgredgffibi.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "cvtx.mm"
include "simp2.mm"
include "opvtxfv.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "3adant2.mm"
include "usgrfilem.mm"
include "syl2anc.mm"
include "opiedgfv.mm"
include "eleq1d.mm"
include "3ad2ant1.mm"
include "3bitr3rd.mm"
include "biimprd.mm"
include "syl5bi.mm"

theorem fusgrfisstep
  let cE: class E
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vp: setvar p

  disjoint E p
  disjoint N p
  disjoint V p
  assert |- ( ( ( V e. X /\ E e. Y ) /\ <. V , E >. e. FinUSGraph /\ N e. V ) -> ( ( _I |` { p e. ( Edg ` <. V , E >. ) | N e/ p } ) e. Fin -> E e. Fin ) )

  proof
    cid
    cN
    vp
    cv
    wnel
    vp
    cV
    cE
    cop
    #
    cedg
    cfv
    #
    crab
    #
    cres
    cfn
    wcel
    @2
    cfn
    wcel
    #
    cV
    cX
    wcel
    cE
    cY
    wcel
    wa
    #
    @0
    cfusgr
    wcel
    #
    cN
    cV
    wcel
    #
    w3a
    #
    cE
    cfn
    wcel
    #
    @2
    residfi
    @7
    @8
    @3
    @7
    @1
    cfn
    wcel
    #
    @0
    ciedg
    cfv
    #
    cfn
    wcel
    #
    @3
    @8
    @5
    @4
    @9
    @11
    wb
    #
    @6
    @5
    @0
    cusgr
    wcel
    @12
    @0
    fusgrusgr
    @1
    @0
    @10
    @10
    eqid
    @1
    eqid
    #
    usgredgffibi
    syl
    3ad2ant2
    @7
    @5
    cN
    @0
    cvtx
    cfv
    #
    wcel
    #
    @9
    @3
    wb
    @4
    @5
    @6
    simp2
    @4
    @6
    @15
    @5
    @4
    @6
    @15
    @4
    cV
    @14
    cN
    @4
    @14
    cV
    cE
    cV
    cX
    cY
    opvtxfv
    eqcomd
    eleq2d
    biimpa
    3adant2
    vp
    @1
    @2
    @0
    cN
    @14
    @14
    eqid
    @13
    @2
    eqid
    usgrfilem
    syl2anc
    @4
    @5
    @11
    @8
    wb
    @6
    @4
    @10
    cE
    cfn
    cE
    cV
    cX
    cY
    opiedgfv
    eleq1d
    3ad2ant1
    3bitr3rd
    biimprd
    syl5bi
end
