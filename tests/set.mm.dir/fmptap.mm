include "cmpt.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fmptsn.mm"
include "mp2an.mm"
include "cv.mm"
include "elsni.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "uneq2i.mm"
include "mptun.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "3eqtr2i.mm"

theorem fmptap
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume fmptap.0a: |- A e. _V
  assume fmptap.0b: |- B e. _V
  assume fmptap.1: |- ( R u. { A } ) = S
  assume fmptap.2: |- ( x = A -> C = B )

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint S x
  assert |- ( ( x e. R |-> C ) u. { <. A , B >. } ) = ( x e. S |-> C )

  proof
    vx
    cR
    cC
    cmpt
    #
    cA
    cB
    cop
    csn
    #
    cun
    @0
    vx
    cA
    csn
    #
    cC
    cmpt
    #
    cun
    vx
    cR
    @2
    cun
    #
    cC
    cmpt
    #
    vx
    cS
    cC
    cmpt
    #
    @1
    @3
    @0
    @1
    vx
    @2
    cB
    cmpt
    #
    @3
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @1
    @7
    wceq
    fmptap.0a
    fmptap.0b
    vx
    cA
    cB
    cvv
    cvv
    fmptsn
    mp2an
    vx
    @2
    cC
    cB
    vx
    cv
    #
    @2
    wcel
    @8
    cA
    wceq
    cC
    cB
    wceq
    @8
    cA
    elsni
    fmptap.2
    syl
    mpteq2ia
    eqtr4i
    uneq2i
    vx
    cR
    @2
    cC
    mptun
    @4
    cS
    wceq
    @5
    @6
    wceq
    fmptap.1
    vx
    @4
    cS
    cC
    mpteq1
    ax-mp
    3eqtr2i
end
