include "cvc.mm"
include "wcel.mm"
include "cgr.mm"
include "co.mm"
include "wceq.mm"
include "vcgrp.mm"
include "grporid.mm"
include "sylan.mm"

theorem vc0rid
  let cA: class A
  let cG: class G
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume vczcl.1: |- G = ( 1st ` W )
  assume vczcl.2: |- X = ran G
  assume vczcl.3: |- Z = ( GId ` G )


  assert |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G Z ) = A )

  proof
    cW
    cvc
    wcel
    cG
    cgr
    wcel
    cA
    cX
    wcel
    cA
    cZ
    cG
    co
    cA
    wceq
    cG
    cW
    vczcl.1
    vcgrp
    cA
    cZ
    cG
    cX
    vczcl.2
    vczcl.3
    grporid
    sylan
end
