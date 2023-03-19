include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wceq.mm"
include "frnsuppeq.mm"
include "3impia.mm"
include "imaeq2i.mm"
include "syl6eqr.mm"

theorem ffs2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume ffs2.1: |- C = ( B \ { Z } )


  assert |- ( ( A e. V /\ Z e. W /\ F : A --> B ) -> ( F supp Z ) = ( `' F " C ) )

  proof
    cA
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    cA
    cB
    cF
    wf
    #
    w3a
    cF
    cZ
    csupp
    co
    #
    cF
    ccnv
    #
    cB
    cZ
    csn
    cdif
    #
    cima
    #
    @4
    cC
    cima
    @0
    @1
    @2
    @3
    @6
    wceq
    cB
    cF
    cA
    cV
    cW
    cZ
    frnsuppeq
    3impia
    cC
    @5
    @4
    ffs2.1
    imaeq2i
    syl6eqr
end
