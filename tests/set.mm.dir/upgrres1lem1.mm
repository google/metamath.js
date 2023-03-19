include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cvtx.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexi.mm"
include "cv.mm"
include "wnel.mm"
include "cedg.mm"
include "rabex2.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "pm3.2i.mm"

theorem upgrres1lem1
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  assume upgrres1.v: |- V = ( Vtx ` G )
  assume upgrres1.e: |- E = ( Edg ` G )
  assume upgrres1.f: |- F = { e e. E | N e/ e }

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  assert |- ( ( V \ { N } ) e. _V /\ ( _I |` F ) e. _V )

  proof
    cV
    cN
    csn
    #
    cdif
    cvv
    wcel
    cid
    cF
    cres
    cvv
    wcel
    #
    cV
    @0
    cV
    cG
    cvtx
    cfv
    cvv
    upgrres1.v
    cG
    cvtx
    fvex
    eqeltri
    difexi
    cF
    cvv
    wcel
    @1
    cN
    ve
    cv
    wnel
    ve
    cE
    cF
    upgrres1.f
    cE
    cG
    cedg
    cfv
    cvv
    upgrres1.e
    cG
    cedg
    fvex
    eqeltri
    rabex2
    cF
    cvv
    resiexg
    ax-mp
    pm3.2i
end
