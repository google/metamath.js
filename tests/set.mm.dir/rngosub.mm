include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "rngogrpo.mm"
include "grpodivval.mm"
include "syl3an1.mm"

theorem rngosub
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cG: class G
  let cN: class N
  let cX: class X
  assume ringnegcl.1: |- G = ( 1st ` R )
  assume ringnegcl.2: |- X = ran G
  assume ringnegcl.3: |- N = ( inv ` G )
  assume ringsub.4: |- D = ( /g ` G )


  assert |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A D B ) = ( A G ( N ` B ) ) )

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
    cD
    co
    cA
    cB
    cN
    cfv
    cG
    co
    wceq
    cR
    cG
    ringnegcl.1
    rngogrpo
    cA
    cB
    cD
    cG
    cN
    cX
    ringnegcl.2
    ringnegcl.3
    ringsub.4
    grpodivval
    syl3an1
end
