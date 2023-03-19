include "wcel.mm"
include "wf1.mm"
include "wa.mm"
include "cvv.mm"
include "crn.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wf.mm"
include "f1f.mm"
include "anim2i.mm"
include "ancomd.mm"
include "fex.mm"
include "syl.mm"
include "c2nd.mm"
include "cres.mm"
include "wi.mm"
include "f1o2ndf1.mm"
include "wfun.mm"
include "csn.mm"
include "cuni.mm"
include "df-2nd.mm"
include "funmpt2.mm"
include "resfunexg.mm"
include "sylancr.mm"
include "f1oeq1.mm"
include "biimpd.mm"
include "eqcoms.mm"
include "adantl.mm"
include "spcimedv.mm"
include "ex.mm"
include "com13.mm"
include "mpcom.mm"
include "impcom.mm"
include "hasheqf1oi.mm"
include "sylc.mm"

theorem hashf1rn
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vf: setvar f
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A -1-1-> B ) -> ( # ` F ) = ( # ` ran F ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    wa
    #
    cF
    cvv
    wcel
    #
    cF
    cF
    crn
    #
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cF
    chash
    cfv
    @4
    chash
    cfv
    wceq
    @2
    cA
    cB
    cF
    wf
    #
    @0
    wa
    @3
    @2
    @0
    @8
    @1
    @8
    @0
    cA
    cB
    cF
    f1f
    anim2i
    ancomd
    cA
    cB
    cV
    cF
    fex
    syl
    #
    @1
    @0
    @7
    cF
    @4
    c2nd
    cF
    cres
    #
    wf1o
    #
    @1
    @0
    @7
    wi
    cA
    cB
    cF
    f1o2ndf1
    @0
    @1
    @11
    @7
    @0
    @1
    @11
    @7
    wi
    @2
    @6
    @11
    vf
    @10
    cvv
    @2
    c2nd
    wfun
    @3
    @10
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
    @9
    c2nd
    cF
    cvv
    resfunexg
    sylancr
    @5
    @10
    wceq
    @11
    @6
    wi
    #
    @2
    @12
    @10
    @5
    @10
    @5
    wceq
    @11
    @6
    cF
    @4
    @10
    @5
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
    hasheqf1oi
    sylc
end
