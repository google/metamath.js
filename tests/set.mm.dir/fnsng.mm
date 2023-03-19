include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "funsng.mm"
include "dmsnopg.mm"
include "adantl.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fnsng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> { <. A , B >. } Fn { A } )

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
    cA
    cB
    cop
    csn
    #
    wfun
    @2
    cdm
    cA
    csn
    #
    wceq
    #
    @2
    @3
    wfn
    cA
    cB
    cV
    cW
    funsng
    @1
    @4
    @0
    cA
    cB
    cW
    dmsnopg
    adantl
    @2
    @3
    df-fn
    sylanbrc
end
