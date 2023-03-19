include "cres.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "fssres.mm"
include "wb.mm"
include "resabs1.mm"
include "feq1d.mm"
include "adantl.mm"
include "mpbid.mm"

theorem fssres2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( ( F |` A ) : A --> B /\ C C_ A ) -> ( F |` C ) : C --> B )

  proof
    cA
    cB
    cF
    cA
    cres
    #
    wf
    #
    cC
    cA
    wss
    #
    wa
    cC
    cB
    @0
    cC
    cres
    #
    wf
    #
    cC
    cB
    cF
    cC
    cres
    #
    wf
    #
    cA
    cB
    cC
    @0
    fssres
    @2
    @4
    @6
    wb
    @1
    @2
    cC
    cB
    @3
    @5
    cF
    cC
    cA
    resabs1
    feq1d
    adantl
    mpbid
end
