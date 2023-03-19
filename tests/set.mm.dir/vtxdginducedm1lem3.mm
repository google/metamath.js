include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cres.mm"
include "vtxdginducedm1lem1.mm"
include "eqtri.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"

theorem vtxdginducedm1lem3
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  assume vtxdginducedm1.v: |- V = ( Vtx ` G )
  assume vtxdginducedm1.e: |- E = ( iEdg ` G )
  assume vtxdginducedm1.k: |- K = ( V \ { N } )
  assume vtxdginducedm1.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume vtxdginducedm1.p: |- P = ( E |` I )
  assume vtxdginducedm1.s: |- S = <. K , P >.

  disjoint E i
  assert |- ( H e. I -> ( ( iEdg ` S ) ` H ) = ( E ` H ) )

  proof
    cH
    cI
    wcel
    cH
    cS
    ciedg
    cfv
    #
    cfv
    cH
    cE
    cI
    cres
    #
    cfv
    cH
    cE
    cfv
    cH
    @0
    @1
    @0
    cP
    @1
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
    vtxdginducedm1.p
    eqtri
    fveq1i
    cH
    cI
    cE
    fvres
    syl5eq
end
