include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "difss.mm"
include "eqid.mm"
include "islsat.mm"
include "biimpa.mm"
include "ssrexv.mm"
include "mpsyl.mm"

theorem islsati
  let vv: setvar v
  let cA: class A
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume islsati.v: |- V = ( Base ` W )
  assume islsati.n: |- N = ( LSpan ` W )
  assume islsati.a: |- A = ( LSAtoms ` W )

  disjoint N v
  disjoint U v
  disjoint V v
  disjoint W v
  disjoint X v
  assert |- ( ( W e. X /\ U e. A ) -> E. v e. V U = ( N ` { v } ) )

  proof
    cV
    cW
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    cV
    wss
    cW
    cX
    wcel
    #
    cU
    cA
    wcel
    #
    wa
    cU
    vv
    cv
    csn
    cN
    cfv
    wceq
    #
    vv
    @2
    wrex
    #
    @5
    vv
    cV
    wrex
    cV
    @1
    difss
    @3
    @4
    @6
    vv
    cA
    cU
    cN
    cV
    cW
    cX
    @0
    islsati.v
    islsati.n
    @0
    eqid
    islsati.a
    islsat
    biimpa
    @5
    vv
    @2
    cV
    ssrexv
    mpsyl
end
