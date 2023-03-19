include "ciedg.mm"
include "cfv.mm"
include "cop.mm"
include "fveq2i.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvexi.mm"
include "difexi.mm"
include "eqeltri.mm"
include "cres.mm"
include "resex.mm"
include "opiedgfvi.mm"
include "eqtri.mm"

theorem vtxdginducedm1lem1
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cG: class G
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


  assert |- ( iEdg ` S ) = P

  proof
    cS
    ciedg
    cfv
    cK
    cP
    cop
    #
    ciedg
    cfv
    cP
    cS
    @0
    ciedg
    vtxdginducedm1.s
    fveq2i
    cP
    cK
    cK
    cV
    cN
    csn
    #
    cdif
    cvv
    vtxdginducedm1.k
    cV
    @1
    cV
    cG
    cvtx
    vtxdginducedm1.v
    fvexi
    difexi
    eqeltri
    cP
    cE
    cI
    cres
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
    opiedgfvi
    eqtri
end
