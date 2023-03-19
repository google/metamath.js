include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "rngoidmlem.mm"
include "simprd.mm"

theorem rngoridm
  let cA: class A
  let cR: class R
  let cU: class U
  let cH: class H
  let cX: class X
  assume uridm.1: |- H = ( 2nd ` R )
  assume uridm.2: |- X = ran ( 1st ` R )
  assume uridm2.2: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( A H U ) = A )

  proof
    cR
    crngo
    wcel
    cA
    cX
    wcel
    wa
    cU
    cA
    cH
    co
    cA
    wceq
    cA
    cU
    cH
    co
    cA
    wceq
    cA
    cR
    cU
    cH
    cX
    uridm.1
    uridm.2
    uridm2.2
    rngoidmlem
    simprd
end
