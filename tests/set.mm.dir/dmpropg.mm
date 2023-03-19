include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "cdm.mm"
include "cun.mm"
include "cpr.mm"
include "wceq.mm"
include "dmsnopg.mm"
include "uneq12.mm"
include "syl2an.mm"
include "df-pr.mm"
include "dmeqi.mm"
include "dmun.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem dmpropg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. V /\ D e. W ) -> dom { <. A , B >. , <. C , D >. } = { A , C } )

  proof
    cB
    cV
    wcel
    #
    cD
    cW
    wcel
    #
    wa
    cA
    cB
    cop
    #
    csn
    #
    cdm
    #
    cC
    cD
    cop
    #
    csn
    #
    cdm
    #
    cun
    #
    cA
    csn
    #
    cC
    csn
    #
    cun
    #
    @2
    @5
    cpr
    #
    cdm
    #
    cA
    cC
    cpr
    @0
    @4
    @9
    wceq
    @7
    @10
    wceq
    @8
    @11
    wceq
    @1
    cA
    cB
    cV
    dmsnopg
    cC
    cD
    cW
    dmsnopg
    @4
    @9
    @7
    @10
    uneq12
    syl2an
    @13
    @3
    @6
    cun
    #
    cdm
    @8
    @12
    @14
    @2
    @5
    df-pr
    dmeqi
    @3
    @6
    dmun
    eqtri
    cA
    cC
    df-pr
    3eqtr4g
end
