include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cres.mm"
include "vtxdginducedm1lem1.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wnel.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssdmres.mm"
include "mpbi.mm"

theorem vtxdginducedm1lem2
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

  disjoint E i
  assert |- dom ( iEdg ` S ) = I

  proof
    cS
    ciedg
    cfv
    #
    cdm
    cE
    cI
    cres
    #
    cdm
    #
    cI
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
    dmeqi
    cI
    cE
    cdm
    #
    wss
    @2
    cI
    wceq
    cI
    cN
    vi
    cv
    cE
    cfv
    wnel
    #
    vi
    @3
    crab
    @3
    vtxdginducedm1.i
    @4
    vi
    @3
    ssrab2
    eqsstri
    cI
    cE
    ssdmres
    mpbi
    eqtri
end
