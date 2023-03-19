include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "upgrres1lem1.mm"
include "opvtxfv.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem upgrres1lem2
  let cS: class S
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  assume upgrres1.v: |- V = ( Vtx ` G )
  assume upgrres1.e: |- E = ( Edg ` G )
  assume upgrres1.f: |- F = { e e. E | N e/ e }
  assume upgrres1.s: |- S = <. ( V \ { N } ) , ( _I |` F ) >.

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint F p
  disjoint G p
  disjoint N p
  disjoint V p
  disjoint e p
  assert |- ( Vtx ` S ) = ( V \ { N } )

  proof
    cS
    cvtx
    cfv
    cV
    cN
    csn
    cdif
    #
    cid
    cF
    cres
    #
    cop
    #
    cvtx
    cfv
    #
    @0
    cS
    @2
    cvtx
    upgrres1.s
    fveq2i
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    wa
    @3
    @0
    wceq
    ve
    cE
    cF
    cG
    cN
    cV
    upgrres1.v
    upgrres1.e
    upgrres1.f
    upgrres1lem1
    @1
    @0
    cvv
    cvv
    opvtxfv
    ax-mp
    eqtri
end
