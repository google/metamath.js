include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "rngogrpo.mm"
include "grpoass.mm"
include "sylan.mm"

theorem rngoaass
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cG: class G
  let cX: class X
  assume ringgcl.1: |- G = ( 1st ` R )
  assume ringgcl.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( A G ( B G C ) ) )

  proof
    cR
    crngo
    wcel
    cG
    cgr
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    cG
    co
    cC
    cG
    co
    cA
    cB
    cC
    cG
    co
    cG
    co
    wceq
    cR
    cG
    ringgcl.1
    rngogrpo
    cA
    cB
    cC
    cG
    cX
    ringgcl.2
    grpoass
    sylan
end
