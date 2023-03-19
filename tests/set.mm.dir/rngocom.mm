include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "co.mm"
include "wceq.mm"
include "rngoablo.mm"
include "ablocom.mm"
include "syl3an1.mm"

theorem rngocom
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cX: class X
  assume ringgcl.1: |- G = ( 1st ` R )
  assume ringgcl.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A G B ) = ( B G A ) )

  proof
    cR
    crngo
    wcel
    cG
    cablo
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cG
    co
    cB
    cA
    cG
    co
    wceq
    cR
    cG
    ringgcl.1
    rngoablo
    cA
    cB
    cG
    cX
    ringgcl.2
    ablocom
    syl3an1
end
