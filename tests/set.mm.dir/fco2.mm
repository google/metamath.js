include "cres.mm"
include "wf.mm"
include "wa.mm"
include "ccom.mm"
include "fco.mm"
include "wceq.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "cores.mm"
include "syl.mm"
include "adantl.mm"
include "feq1d.mm"
include "mpbid.mm"

theorem fco2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( ( F |` B ) : B --> C /\ G : A --> B ) -> ( F o. G ) : A --> C )

  proof
    cB
    cC
    cF
    cB
    cres
    #
    wf
    #
    cA
    cB
    cG
    wf
    #
    wa
    #
    cA
    cC
    @0
    cG
    ccom
    #
    wf
    cA
    cC
    cF
    cG
    ccom
    #
    wf
    cA
    cB
    cC
    @0
    cG
    fco
    @3
    cA
    cC
    @4
    @5
    @2
    @4
    @5
    wceq
    #
    @1
    @2
    cG
    crn
    cB
    wss
    @6
    cA
    cB
    cG
    frn
    cF
    cG
    cB
    cores
    syl
    adantl
    feq1d
    mpbid
end
