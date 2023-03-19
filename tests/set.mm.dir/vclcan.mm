include "cvc.mm"
include "wcel.mm"
include "cgr.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "vcgrp.mm"
include "grpolcan.mm"
include "sylan.mm"

theorem vclcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cW: class W
  let cX: class X
  assume vclcan.1: |- G = ( 1st ` W )
  assume vclcan.2: |- X = ran G


  assert |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( C G A ) = ( C G B ) <-> A = B ) )

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
    cB
    cX
    wcel
    cC
    cX
    wcel
    w3a
    cC
    cA
    cG
    co
    cC
    cB
    cG
    co
    wceq
    cA
    cB
    wceq
    wb
    cG
    cW
    vclcan.1
    vcgrp
    cA
    cB
    cC
    cG
    cX
    vclcan.2
    grpolcan
    sylan
end
