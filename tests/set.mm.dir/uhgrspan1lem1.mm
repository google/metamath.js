include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "wcel.mm"
include "cres.mm"
include "cvtx.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexi.mm"
include "ciedg.mm"
include "resex.mm"
include "pm3.2i.mm"

theorem uhgrspan1lem1
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  assume uhgrspan1.v: |- V = ( Vtx ` G )
  assume uhgrspan1.i: |- I = ( iEdg ` G )
  assume uhgrspan1.f: |- F = { i e. dom I | N e/ ( I ` i ) }


  assert |- ( ( V \ { N } ) e. _V /\ ( I |` F ) e. _V )

  proof
    cV
    cN
    csn
    #
    cdif
    cvv
    wcel
    cI
    cF
    cres
    cvv
    wcel
    cV
    @0
    cV
    cG
    cvtx
    cfv
    cvv
    uhgrspan1.v
    cG
    cvtx
    fvex
    eqeltri
    difexi
    cI
    cF
    cI
    cG
    ciedg
    cfv
    cvv
    uhgrspan1.i
    cG
    ciedg
    fvex
    eqeltri
    resex
    pm3.2i
end
