include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "rngogrpo.mm"
include "grpolinv.mm"
include "sylan.mm"

theorem rngoaddneg2
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume ringnegcl.1: |- G = ( 1st ` R )
  assume ringnegcl.2: |- X = ran G
  assume ringnegcl.3: |- N = ( inv ` G )
  assume ringaddneg.4: |- Z = ( GId ` G )


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( ( N ` A ) G A ) = Z )

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
    cA
    cG
    co
    cZ
    wceq
    cR
    cG
    ringnegcl.1
    rngogrpo
    cA
    cZ
    cG
    cN
    cX
    ringnegcl.2
    ringaddneg.4
    ringnegcl.3
    grpolinv
    sylan
end
