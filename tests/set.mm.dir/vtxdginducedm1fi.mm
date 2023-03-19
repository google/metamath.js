include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "crab.mm"
include "chash.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "caddc.mm"
include "vtxdginducedm1.mm"
include "wa.mm"
include "cdm.mm"
include "cn0.mm"
include "cres.mm"
include "dmeqi.mm"
include "finresfin.mm"
include "dmfi.mm"
include "syl.mm"
include "syl5eqel.mm"
include "cvtx.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "fvexi.mm"
include "difexi.mm"
include "eqeltri.mm"
include "ciedg.mm"
include "resex.mm"
include "opvtxfvi.mm"
include "3eqtrri.mm"
include "vtxdginducedm1lem1.mm"
include "eqcomi.mm"
include "eqid.mm"
include "vtxdgfisnn0.mm"
include "sylan.mm"
include "nn0red.mm"
include "rabfi.mm"
include "hashcl.mm"
include "3syl.mm"
include "adantr.mm"
include "rexaddd.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "mpi.mm"

theorem vtxdginducedm1fi
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
  let vl: setvar l
  let vk: setvar k
  let cW: class W
  assume vtxdginducedm1.v: |- V = ( Vtx ` G )
  assume vtxdginducedm1.e: |- E = ( iEdg ` G )
  assume vtxdginducedm1.k: |- K = ( V \ { N } )
  assume vtxdginducedm1.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume vtxdginducedm1.p: |- P = ( E |` I )
  assume vtxdginducedm1.s: |- S = <. K , P >.
  assume vtxdginducedm1.j: |- J = { i e. dom E | N e. ( E ` i ) }

  disjoint E i
  disjoint N i
  disjoint E l
  disjoint J l
  disjoint l v
  disjoint E v
  disjoint J k
  disjoint N k
  disjoint i k
  disjoint V k
  disjoint W k
  disjoint E k
  disjoint k l
  disjoint G k
  disjoint I k
  disjoint S k
  disjoint k v
  assert |- ( E e. Fin -> A. v e. ( V \ { N } ) ( ( VtxDeg ` G ) ` v ) = ( ( ( VtxDeg ` S ) ` v ) + ( # ` { l e. J | v e. ( E ` l ) } ) ) )

  proof
    cE
    cfn
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    cfv
    #
    @1
    cS
    cvtxdg
    cfv
    cfv
    #
    @1
    vl
    cv
    cE
    cfv
    wcel
    #
    vl
    cJ
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    wceq
    #
    vv
    cV
    cN
    csn
    #
    cdif
    #
    wral
    @2
    @3
    @6
    caddc
    co
    #
    wceq
    #
    vv
    @10
    wral
    vv
    cP
    cS
    vi
    cE
    cG
    cI
    cJ
    cK
    cN
    cV
    vl
    vtxdginducedm1.v
    vtxdginducedm1.e
    vtxdginducedm1.k
    vtxdginducedm1.i
    vtxdginducedm1.p
    vtxdginducedm1.s
    vtxdginducedm1.j
    vtxdginducedm1
    @0
    @8
    @12
    vv
    @10
    @0
    @1
    @10
    wcel
    #
    wa
    #
    @8
    @12
    @14
    @7
    @11
    @2
    @14
    @3
    @6
    @14
    @3
    @0
    cP
    cdm
    #
    cfn
    wcel
    @13
    @3
    cn0
    wcel
    @0
    @15
    cE
    cI
    cres
    #
    cdm
    #
    cfn
    cP
    @16
    vtxdginducedm1.p
    dmeqi
    @0
    @16
    cfn
    wcel
    @17
    cfn
    wcel
    cI
    cE
    finresfin
    @16
    dmfi
    syl
    syl5eqel
    @15
    @1
    cS
    cP
    @10
    cS
    cvtx
    cfv
    cK
    cP
    cop
    #
    cvtx
    cfv
    cK
    @10
    cS
    @18
    cvtx
    vtxdginducedm1.s
    fveq2i
    cP
    cK
    cK
    @10
    cvv
    vtxdginducedm1.k
    cV
    @9
    cV
    cG
    cvtx
    vtxdginducedm1.v
    fvexi
    difexi
    eqeltri
    cP
    @16
    cvv
    vtxdginducedm1.p
    cE
    cI
    cE
    cG
    ciedg
    vtxdginducedm1.e
    fvexi
    resex
    eqeltri
    opvtxfvi
    vtxdginducedm1.k
    3eqtrri
    cS
    ciedg
    cfv
    cP
    cP
    cS
    vi
    cE
    cG
    cI
    cK
    cN
    cV
    vtxdginducedm1.v
    vtxdginducedm1.e
    vtxdginducedm1.k
    vtxdginducedm1.i
    vtxdginducedm1.p
    vtxdginducedm1.s
    vtxdginducedm1lem1
    eqcomi
    @15
    eqid
    vtxdgfisnn0
    sylan
    nn0red
    @14
    @6
    @0
    @6
    cn0
    wcel
    #
    @13
    @0
    cJ
    cfn
    wcel
    @5
    cfn
    wcel
    @19
    @0
    cJ
    cN
    vi
    cv
    cE
    cfv
    wcel
    #
    vi
    cE
    cdm
    #
    crab
    #
    cfn
    vtxdginducedm1.j
    @0
    @21
    cfn
    wcel
    @22
    cfn
    wcel
    cE
    dmfi
    @20
    vi
    @21
    rabfi
    syl
    syl5eqel
    @4
    vl
    cJ
    rabfi
    @5
    hashcl
    3syl
    adantr
    nn0red
    rexaddd
    eqeq2d
    biimpd
    ralimdva
    mpi
end
