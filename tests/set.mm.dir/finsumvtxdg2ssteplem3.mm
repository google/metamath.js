include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "crab.mm"
include "chash.mm"
include "csu.mm"
include "wceq.mm"
include "cdm.mm"
include "caddc.mm"
include "co.mm"
include "rabeq2i.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rabbia2.mm"
include "fveq2i.mm"
include "a1i.mm"
include "sumeq2dv.mm"
include "oveq1d.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "numedglnl.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "syl6eqr.mm"

theorem finsumvtxdg2ssteplem3
  let vv: setvar v
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  assume finsumvtxdg2sstep.v: |- V = ( Vtx ` G )
  assume finsumvtxdg2sstep.e: |- E = ( iEdg ` G )
  assume finsumvtxdg2sstep.k: |- K = ( V \ { N } )
  assume finsumvtxdg2sstep.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume finsumvtxdg2sstep.p: |- P = ( E |` I )
  assume finsumvtxdg2sstep.s: |- S = <. K , P >.
  assume finsumvtxdg2ssteplem.j: |- J = { i e. dom E | N e. ( E ` i ) }

  disjoint E v
  disjoint G v
  disjoint N v
  disjoint V i
  disjoint V v
  disjoint i v
  disjoint E i
  disjoint G i
  disjoint N i
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ ( V e. Fin /\ E e. Fin ) ) -> ( sum_ v e. ( V \ { N } ) ( # ` { i e. J | v e. ( E ` i ) } ) + ( # ` { i e. dom E | ( E ` i ) = { N } } ) ) = ( # ` J ) )

  proof
    cG
    cupgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cV
    cfn
    wcel
    cE
    cfn
    wcel
    wa
    #
    wa
    #
    cV
    cN
    csn
    #
    cdif
    #
    vv
    cv
    #
    vi
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vi
    cJ
    crab
    #
    chash
    cfv
    #
    vv
    csu
    #
    @9
    @5
    wceq
    vi
    cE
    cdm
    #
    crab
    chash
    cfv
    #
    caddc
    co
    #
    cN
    @9
    wcel
    #
    vi
    @14
    crab
    #
    chash
    cfv
    #
    cJ
    chash
    cfv
    @4
    @16
    @6
    @17
    @10
    wa
    #
    vi
    @14
    crab
    #
    chash
    cfv
    #
    vv
    csu
    #
    @15
    caddc
    co
    #
    @19
    @4
    @13
    @23
    @15
    caddc
    @4
    @6
    @12
    @22
    vv
    @12
    @22
    wceq
    @4
    @7
    @6
    wcel
    wa
    @11
    @21
    chash
    @10
    @20
    vi
    cJ
    @14
    @8
    cJ
    wcel
    #
    @10
    wa
    @8
    @14
    wcel
    #
    @17
    wa
    #
    @10
    wa
    @26
    @20
    wa
    @25
    @27
    @10
    @17
    vi
    cJ
    @14
    finsumvtxdg2ssteplem.j
    rabeq2i
    anbi1i
    @26
    @17
    @10
    anass
    bitri
    rabbia2
    fveq2i
    a1i
    sumeq2dv
    oveq1d
    @4
    @0
    @3
    @1
    @24
    @19
    wceq
    @0
    @1
    @3
    simpll
    @2
    @3
    simpr
    @0
    @1
    @3
    simplr
    vv
    vi
    cE
    cG
    cN
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    numedglnl
    syl3anc
    eqtrd
    cJ
    @18
    chash
    finsumvtxdg2ssteplem.j
    fveq2i
    syl6eqr
end
