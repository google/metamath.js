include "ciedg.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "uhgrspan1lem1.mm"
include "opiedgfv.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem uhgrspan1lem3
  let cS: class S
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  assume uhgrspan1.v: |- V = ( Vtx ` G )
  assume uhgrspan1.i: |- I = ( iEdg ` G )
  assume uhgrspan1.f: |- F = { i e. dom I | N e/ ( I ` i ) }
  assume uhgrspan1.s: |- S = <. ( V \ { N } ) , ( I |` F ) >.


  assert |- ( iEdg ` S ) = ( I |` F )

  proof
    cS
    ciedg
    cfv
    cV
    cN
    csn
    cdif
    #
    cI
    cF
    cres
    #
    cop
    #
    ciedg
    cfv
    #
    @1
    cS
    @2
    ciedg
    uhgrspan1.s
    fveq2i
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    wa
    @3
    @1
    wceq
    vi
    cF
    cG
    cI
    cN
    cV
    uhgrspan1.v
    uhgrspan1.i
    uhgrspan1.f
    uhgrspan1lem1
    @1
    @0
    cvv
    cvv
    opiedgfv
    ax-mp
    eqtri
end
