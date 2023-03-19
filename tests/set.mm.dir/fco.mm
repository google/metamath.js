include "wf.mm"
include "wa.mm"
include "ccom.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "df-f.mm"
include "wi.mm"
include "fnco.mm"
include "3expib.mm"
include "adantr.mm"
include "rncoss.mm"
include "sstr.mm"
include "mpan.mm"
include "adantl.mm"
include "jctird.mm"
include "imp.mm"
include "syl2anb.mm"
include "sylibr.mm"

theorem fco
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : B --> C /\ G : A --> B ) -> ( F o. G ) : A --> C )

  proof
    cB
    cC
    cF
    wf
    #
    cA
    cB
    cG
    wf
    #
    wa
    cF
    cG
    ccom
    #
    cA
    wfn
    #
    @2
    crn
    #
    cC
    wss
    #
    wa
    #
    cA
    cC
    @2
    wf
    @0
    cF
    cB
    wfn
    #
    cF
    crn
    #
    cC
    wss
    #
    wa
    #
    cG
    cA
    wfn
    #
    cG
    crn
    cB
    wss
    #
    wa
    #
    @6
    @1
    cB
    cC
    cF
    df-f
    cA
    cB
    cG
    df-f
    @10
    @13
    @6
    @10
    @13
    @3
    @5
    @7
    @13
    @3
    wi
    @9
    @7
    @11
    @12
    @3
    cB
    cA
    cF
    cG
    fnco
    3expib
    adantr
    @9
    @5
    @7
    @4
    @8
    wss
    @9
    @5
    cF
    cG
    rncoss
    @4
    @8
    cC
    sstr
    mpan
    adantl
    jctird
    imp
    syl2anb
    cA
    cC
    @2
    df-f
    sylibr
end
