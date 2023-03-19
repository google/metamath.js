include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "co.mm"
include "rngogrpo.mm"
include "grpocl.mm"
include "syl3an1.mm"

theorem rngogcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cX: class X
  assume ringgcl.1: |- G = ( 1st ` R )
  assume ringgcl.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A G B ) e. X )

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
    cA
    cB
    cG
    co
    cX
    wcel
    cR
    cG
    ringgcl.1
    rngogrpo
    cA
    cB
    cG
    cX
    ringgcl.2
    grpocl
    syl3an1
end
