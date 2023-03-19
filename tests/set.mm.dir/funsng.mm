include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "wfun.mm"
include "funcnvsn.mm"
include "wceq.mm"
include "cnvsng.mm"
include "ancoms.mm"
include "funeqd.mm"
include "mpbii.mm"

theorem funsng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> Fun { <. A , B >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cB
    cA
    cop
    csn
    ccnv
    #
    wfun
    cA
    cB
    cop
    csn
    #
    wfun
    cB
    cA
    funcnvsn
    @2
    @3
    @4
    @1
    @0
    @3
    @4
    wceq
    cB
    cA
    cW
    cV
    cnvsng
    ancoms
    funeqd
    mpbii
end
