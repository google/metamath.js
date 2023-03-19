include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "wfn.mm"
include "crn.mm"
include "df-f.mm"
include "fnssres.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "sstr.mm"
include "mpan.mm"
include "anim12i.mm"
include "an32s.mm"
include "sylanb.mm"
include "sylibr.mm"

theorem fssres
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A --> B /\ C C_ A ) -> ( F |` C ) : C --> B )

  proof
    cA
    cB
    cF
    wf
    #
    cC
    cA
    wss
    #
    wa
    cF
    cC
    cres
    #
    cC
    wfn
    #
    @2
    crn
    #
    cB
    wss
    #
    wa
    #
    cC
    cB
    @2
    wf
    @0
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    wa
    @1
    @6
    cA
    cB
    cF
    df-f
    @7
    @1
    @9
    @6
    @7
    @1
    wa
    @3
    @9
    @5
    cA
    cC
    cF
    fnssres
    @4
    @8
    wss
    #
    @9
    @5
    @2
    cF
    wss
    @10
    cF
    cC
    resss
    @2
    cF
    rnss
    ax-mp
    @4
    @8
    cB
    sstr
    mpan
    anim12i
    an32s
    sylanb
    cC
    cB
    @2
    df-f
    sylibr
end
