include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "cnvso.mm"
include "fisupcl.mm"
include "sylanb.mm"
include "syl5eqel.mm"

theorem fiinfcl
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. Fin /\ B =/= (/) /\ B C_ A ) ) -> inf ( B , A , R ) e. B )

  proof
    cA
    cR
    wor
    #
    cB
    cfn
    wcel
    cB
    c0
    wne
    cB
    cA
    wss
    w3a
    #
    wa
    cB
    cA
    cR
    cinf
    cB
    cA
    cR
    ccnv
    #
    csup
    #
    cB
    cB
    cA
    cR
    df-inf
    @0
    cA
    @2
    wor
    @1
    @3
    cB
    wcel
    cA
    cR
    cnvso
    cA
    cB
    @2
    fisupcl
    sylanb
    syl5eqel
end
