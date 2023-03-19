include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "cfv.mm"
include "rngogrpo.mm"
include "grpoinvcl.mm"
include "sylan.mm"

theorem rngonegcl
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cX: class X
  assume ringnegcl.1: |- G = ( 1st ` R )
  assume ringnegcl.2: |- X = ran G
  assume ringnegcl.3: |- N = ( inv ` G )


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( N ` A ) e. X )

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
    cA
    cN
    cfv
    cX
    wcel
    cR
    cG
    ringnegcl.1
    rngogrpo
    cA
    cG
    cN
    cX
    ringnegcl.2
    ringnegcl.3
    grpoinvcl
    sylan
end
