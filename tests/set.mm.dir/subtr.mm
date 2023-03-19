include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "nfeq.mm"
include "nfim.mm"
include "eqeq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "adantr.mm"

theorem subtr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume subtr.1: |- F/_ x A
  assume subtr.2: |- F/_ x B
  assume subtr.3: |- F/_ x Y
  assume subtr.4: |- F/_ x Z
  assume subtr.5: |- ( x = A -> X = Y )
  assume subtr.6: |- ( x = B -> X = Z )


  assert |- ( ( A e. C /\ B e. D ) -> ( A = B -> Y = Z ) )

  proof
    cA
    cC
    wcel
    cA
    cB
    wceq
    #
    cY
    cZ
    wceq
    #
    wi
    #
    cB
    cD
    wcel
    vx
    cv
    #
    cB
    wceq
    #
    cX
    cZ
    wceq
    #
    wi
    @2
    vx
    cA
    cC
    subtr.1
    @0
    @1
    vx
    vx
    cA
    cB
    subtr.1
    subtr.2
    nfeq
    vx
    cY
    cZ
    subtr.3
    subtr.4
    nfeq
    nfim
    @3
    cA
    wceq
    #
    @4
    @0
    @5
    @1
    @3
    cA
    cB
    eqeq1
    @6
    cX
    cY
    cZ
    subtr.5
    eqeq1d
    imbi12d
    subtr.6
    vtoclgf
    adantr
end
