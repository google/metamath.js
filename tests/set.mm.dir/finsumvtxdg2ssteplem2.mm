include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "dmfi.mm"
include "adantl.mm"
include "simpr.mm"
include "eqid.mm"
include "vtxdgfival.mm"
include "syl2anr.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "a1i.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem finsumvtxdg2ssteplem2
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

  disjoint E i
  disjoint G i
  disjoint N i
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ ( V e. Fin /\ E e. Fin ) ) -> ( ( VtxDeg ` G ) ` N ) = ( ( # ` J ) + ( # ` { i e. dom E | ( E ` i ) = { N } } ) ) )

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
    #
    cE
    cfn
    wcel
    #
    wa
    #
    wa
    #
    cN
    cG
    cvtxdg
    cfv
    cfv
    #
    cN
    vi
    cv
    cE
    cfv
    #
    wcel
    vi
    cE
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @8
    cN
    csn
    wceq
    vi
    @9
    crab
    chash
    cfv
    #
    caddc
    co
    #
    cJ
    chash
    cfv
    #
    @12
    caddc
    co
    @5
    @9
    cfn
    wcel
    #
    @1
    @7
    @13
    wceq
    @2
    @4
    @15
    @3
    cE
    dmfi
    adantl
    @0
    @1
    simpr
    vi
    @9
    cN
    cG
    cE
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    @9
    eqid
    vtxdgfival
    syl2anr
    @6
    @11
    @14
    @12
    caddc
    @11
    @14
    wceq
    @6
    @10
    cJ
    chash
    cJ
    @10
    finsumvtxdg2ssteplem.j
    eqcomi
    fveq2i
    a1i
    oveq1d
    eqtrd
end
