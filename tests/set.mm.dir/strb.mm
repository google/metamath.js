include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "cst.mm"
include "wral.mm"
include "wss.mm"
include "stri.mm"
include "wcel.mm"
include "stlesi.mm"
include "com12.mm"
include "ralrimiv.mm"
include "impbii.mm"

theorem strb
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vu: setvar u
  let vx: setvar x
  assume str.1: |- A e. CH
  assume str.2: |- B e. CH

  disjoint A f
  disjoint B f
  disjoint u x
  disjoint f x
  disjoint A x
  disjoint f u
  disjoint A u
  disjoint B x
  disjoint B u
  assert |- ( A. f e. States ( ( f ` A ) = 1 -> ( f ` B ) = 1 ) <-> A C_ B )

  proof
    cA
    vf
    cv
    #
    cfv
    c1
    wceq
    cB
    @0
    cfv
    c1
    wceq
    wi
    #
    vf
    cst
    wral
    cA
    cB
    wss
    #
    cA
    cB
    vf
    str.1
    str.2
    stri
    @2
    @1
    vf
    cst
    @0
    cst
    wcel
    @2
    @1
    cA
    cB
    @0
    str.1
    str.2
    stlesi
    com12
    ralrimiv
    impbii
end
