include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "adantr.mm"
include "cdm.mm"
include "simpr.mm"
include "wfun.mm"
include "frege126d.mm"
include "biid.mm"
include "eqcom.mm"
include "3orbi123i.mm"
include "sylib.mm"
include "3orcomb.mm"
include "3orrot.mm"
include "sylbb.mm"
include "syl.mm"
include "ex.mm"
include "eqcomd.mm"
include "wi.mm"
include "funbrfvb.mm"
include "biimpd.mm"
include "syl2anc.mm"
include "mpd.mm"
include "frege91d.mm"
include "eqbrtrrd.mm"
include "3mix1.mm"
include "syl6.mm"
include "wrel.mm"
include "funrel.mm"
include "reltrclfv.mm"
include "brrelex.mm"
include "sylan.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "elex.mm"
include "frege96d.mm"
include "3jaod.mm"

theorem frege129d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume frege129d.f: |- ( ph -> F e. _V )
  assume frege129d.a: |- ( ph -> A e. dom F )
  assume frege129d.c: |- ( ph -> C = ( F ` A ) )
  assume frege129d.or: |- ( ph -> ( A ( t+ ` F ) B \/ A = B \/ B ( t+ ` F ) A ) )
  assume frege129d.fun: |- ( ph -> Fun F )


  assert |- ( ph -> ( B ( t+ ` F ) C \/ B = C \/ C ( t+ ` F ) B ) )

  proof
    wph
    cA
    cB
    cF
    ctcl
    cfv
    #
    wbr
    #
    cA
    cB
    wceq
    #
    cB
    cA
    @0
    wbr
    #
    w3o
    cB
    cC
    @0
    wbr
    #
    cB
    cC
    wceq
    #
    cC
    cB
    @0
    wbr
    #
    w3o
    #
    frege129d.or
    wph
    @1
    @7
    @2
    @3
    wph
    @1
    @7
    wph
    @1
    wa
    #
    @6
    @5
    @4
    w3o
    #
    @7
    @8
    @6
    cC
    cB
    wceq
    #
    @4
    w3o
    @9
    @8
    cC
    cB
    cF
    cA
    wph
    cF
    cvv
    wcel
    #
    @1
    frege129d.f
    adantr
    wph
    cA
    cF
    cdm
    #
    wcel
    #
    @1
    frege129d.a
    adantr
    wph
    cC
    cA
    cF
    cfv
    #
    wceq
    @1
    frege129d.c
    adantr
    wph
    @1
    simpr
    wph
    cF
    wfun
    #
    @1
    frege129d.fun
    adantr
    frege126d
    @6
    @6
    @10
    @5
    @4
    @4
    @6
    biid
    cC
    cB
    eqcom
    @4
    biid
    3orbi123i
    sylib
    @9
    @6
    @4
    @5
    w3o
    @7
    @6
    @5
    @4
    3orcomb
    @6
    @4
    @5
    3orrot
    sylbb
    syl
    ex
    wph
    @2
    @4
    @7
    wph
    @2
    @4
    wph
    @2
    wa
    cA
    cB
    cC
    @0
    wph
    @2
    simpr
    wph
    cA
    cC
    @0
    wbr
    @2
    wph
    cA
    cC
    cF
    frege129d.f
    wph
    @14
    cC
    wceq
    #
    cA
    cC
    cF
    wbr
    #
    wph
    cC
    @14
    frege129d.c
    eqcomd
    wph
    @15
    @13
    @16
    @17
    wi
    frege129d.fun
    frege129d.a
    @15
    @13
    wa
    @16
    @17
    cA
    cC
    cF
    funbrfvb
    biimpd
    syl2anc
    mpd
    #
    frege91d
    adantr
    eqbrtrrd
    ex
    @4
    @5
    @6
    3mix1
    #
    syl6
    wph
    @3
    @4
    @7
    wph
    @3
    @4
    wph
    @3
    wa
    cB
    cC
    cA
    cF
    wph
    @11
    @3
    frege129d.f
    adantr
    wph
    @0
    wrel
    #
    @3
    cB
    cvv
    wcel
    wph
    @11
    cF
    wrel
    #
    @20
    frege129d.f
    wph
    @15
    @21
    frege129d.fun
    cF
    funrel
    syl
    cF
    cvv
    reltrclfv
    syl2anc
    cB
    cA
    @0
    brrelex
    sylan
    wph
    cC
    cvv
    wcel
    @3
    wph
    cC
    @14
    cvv
    frege129d.c
    cA
    cF
    fvex
    syl6eqel
    adantr
    wph
    cA
    cvv
    wcel
    #
    @3
    wph
    @13
    @22
    frege129d.a
    cA
    @12
    elex
    syl
    adantr
    wph
    @3
    simpr
    wph
    @17
    @3
    @18
    adantr
    frege96d
    ex
    @19
    syl6
    3jaod
    mpd
end
