include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "frege96d.mm"
include "eqbrtrd.mm"
include "frege91d.mm"
include "mpjaodan.mm"

theorem frege102d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume frege102d.r: |- ( ph -> R e. _V )
  assume frege102d.a: |- ( ph -> A e. _V )
  assume frege102d.b: |- ( ph -> B e. _V )
  assume frege102d.c: |- ( ph -> C e. _V )
  assume frege102d.ac: |- ( ph -> ( A ( t+ ` R ) C \/ A = C ) )
  assume frege102d.cb: |- ( ph -> C R B )


  assert |- ( ph -> A ( t+ ` R ) B )

  proof
    wph
    cA
    cC
    cR
    ctcl
    cfv
    #
    wbr
    #
    cA
    cB
    @0
    wbr
    cA
    cC
    wceq
    #
    wph
    @1
    wa
    cA
    cB
    cC
    cR
    wph
    cR
    cvv
    wcel
    #
    @1
    frege102d.r
    adantr
    wph
    cA
    cvv
    wcel
    @1
    frege102d.a
    adantr
    wph
    cB
    cvv
    wcel
    @1
    frege102d.b
    adantr
    wph
    cC
    cvv
    wcel
    @1
    frege102d.c
    adantr
    wph
    @1
    simpr
    wph
    cC
    cB
    cR
    wbr
    #
    @1
    frege102d.cb
    adantr
    frege96d
    wph
    @2
    wa
    #
    cA
    cB
    cR
    wph
    @3
    @2
    frege102d.r
    adantr
    @5
    cA
    cC
    cB
    cR
    wph
    @2
    simpr
    wph
    @4
    @2
    frege102d.cb
    adantr
    eqbrtrd
    frege91d
    frege102d.ac
    mpjaodan
end
