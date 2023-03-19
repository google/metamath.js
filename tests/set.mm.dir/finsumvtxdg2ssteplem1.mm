include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cres.mm"
include "cdm.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wfun.mm"
include "wss.mm"
include "wceq.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "cv.mm"
include "wnel.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "hashreshashfun.mm"
include "syl3anc.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "wn.mm"
include "notrab.mm"
include "difeq2i.mm"
include "nnel.mm"
include "bicomi.mm"
include "rabbii.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem finsumvtxdg2ssteplem1
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
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ ( V e. Fin /\ E e. Fin ) ) -> ( # ` E ) = ( ( # ` P ) + ( # ` J ) ) )

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
    cE
    chash
    cfv
    #
    cE
    cI
    cres
    #
    chash
    cfv
    #
    cE
    cdm
    #
    cI
    cdif
    #
    chash
    cfv
    #
    caddc
    co
    #
    cP
    chash
    cfv
    #
    cJ
    chash
    cfv
    #
    caddc
    co
    @6
    cE
    wfun
    #
    @4
    cI
    @10
    wss
    #
    @7
    @13
    wceq
    @0
    @16
    @1
    @5
    @0
    cG
    cuhgr
    wcel
    @16
    cG
    upgruhgr
    cE
    cG
    finsumvtxdg2sstep.e
    uhgrfun
    syl
    ad2antrr
    @2
    @3
    @4
    simprr
    @17
    @6
    cI
    cN
    vi
    cv
    cE
    cfv
    #
    wnel
    #
    vi
    @10
    crab
    #
    @10
    finsumvtxdg2sstep.i
    @19
    vi
    @10
    ssrab2
    eqsstri
    a1i
    cE
    cI
    hashreshashfun
    syl3anc
    @6
    @9
    @14
    @12
    @15
    caddc
    @9
    @14
    wceq
    @6
    @8
    cP
    chash
    cP
    @8
    finsumvtxdg2sstep.p
    eqcomi
    fveq2i
    a1i
    @6
    @11
    cJ
    chash
    @11
    cJ
    wceq
    @6
    @10
    @20
    cdif
    @19
    wn
    #
    vi
    @10
    crab
    #
    @11
    cJ
    @19
    vi
    @10
    notrab
    cI
    @20
    @10
    finsumvtxdg2sstep.i
    difeq2i
    cJ
    cN
    @18
    wcel
    #
    vi
    @10
    crab
    @22
    finsumvtxdg2ssteplem.j
    @23
    @21
    vi
    @10
    @21
    @23
    cN
    @18
    nnel
    bicomi
    rabbii
    eqtri
    3eqtr4i
    a1i
    fveq2d
    oveq12d
    eqtrd
end
