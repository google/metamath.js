include "wcel.mm"
include "wa.mm"
include "wf1.mm"
include "chash.mm"
include "cfv.mm"
include "crn.mm"
include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wi.mm"
include "wf.mm"
include "f1f.mm"
include "fex.mm"
include "ex.mm"
include "syl.mm"
include "com12.mm"
include "adantr.mm"
include "imp.mm"
include "rnexg.mm"
include "jccir.mm"
include "c2nd.mm"
include "cres.mm"
include "f1o2ndf1.mm"
include "wfun.mm"
include "csn.mm"
include "cuni.mm"
include "df-2nd.mm"
include "funmpt2.mm"
include "expcom.mm"
include "syl5com.mm"
include "impcom.mm"
include "resfunexg.mm"
include "sylancr.mm"
include "f1oeq1.mm"
include "biimpd.mm"
include "eqcoms.mm"
include "adantl.mm"
include "spcimedv.mm"
include "com13.mm"
include "mpcom.mm"
include "hasheqf1oiOLD.mm"
include "sylc.mm"

theorem hashf1rnOLD
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. W ) -> ( F : A -1-1-> B -> ( # ` F ) = ( # ` ran F ) ) )

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
    cA
    cB
    cF
    wf1
    #
    cF
    chash
    cfv
    cF
    crn
    #
    chash
    cfv
    wceq
    #
    @2
    @3
    wa
    #
    cF
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    wa
    cF
    @4
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @5
    @6
    @7
    @8
    @2
    @3
    @7
    @0
    @3
    @7
    wi
    @1
    @3
    @0
    @7
    @3
    cA
    cB
    cF
    wf
    #
    @0
    @7
    wi
    cA
    cB
    cF
    f1f
    #
    @12
    @0
    @7
    cA
    cB
    cV
    cF
    fex
    #
    ex
    syl
    com12
    adantr
    imp
    cF
    cvv
    rnexg
    jccir
    @3
    @2
    @11
    cF
    @4
    c2nd
    cF
    cres
    #
    wf1o
    #
    @3
    @2
    @11
    wi
    cA
    cB
    cF
    f1o2ndf1
    @2
    @3
    @16
    @11
    @2
    @3
    @16
    @11
    wi
    @6
    @10
    @16
    vf
    @15
    cvv
    @6
    c2nd
    wfun
    @7
    @15
    cvv
    wcel
    vx
    cvv
    vx
    cv
    csn
    crn
    cuni
    c2nd
    vx
    df-2nd
    funmpt2
    @3
    @2
    @7
    @3
    @12
    @2
    @7
    @13
    @0
    @12
    @7
    wi
    @1
    @12
    @0
    @7
    @14
    expcom
    adantr
    syl5com
    impcom
    c2nd
    cF
    cvv
    resfunexg
    sylancr
    @9
    @15
    wceq
    @16
    @10
    wi
    #
    @6
    @17
    @15
    @9
    @15
    @9
    wceq
    @16
    @10
    cF
    @4
    @15
    @9
    f1oeq1
    biimpd
    eqcoms
    adantl
    spcimedv
    ex
    com13
    mpcom
    impcom
    cF
    @4
    vf
    cvv
    cvv
    hasheqf1oiOLD
    sylc
    ex
end
