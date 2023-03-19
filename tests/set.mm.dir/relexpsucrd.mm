include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crelexp.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wrel.mm"
include "adantr.mm"
include "simpr.mm"
include "relexpsucr.mm"
include "syl3anc.mm"
include "ex.mm"

theorem relexpsucrd
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexpsucrd.1: |- ( ph -> Rel R )
  assume relexpsucrd.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> ( R ^r ( N + 1 ) ) = ( ( R ^r N ) o. R ) ) )

  proof
    wph
    cN
    cn0
    wcel
    #
    cR
    cN
    c1
    caddc
    co
    crelexp
    co
    cR
    cN
    crelexp
    co
    cR
    ccom
    wceq
    #
    wph
    @0
    wa
    cR
    cvv
    wcel
    #
    cR
    wrel
    #
    @0
    @1
    wph
    @2
    @0
    relexpsucrd.2
    adantr
    wph
    @3
    @0
    relexpsucrd.1
    adantr
    wph
    @0
    simpr
    cR
    cN
    cvv
    relexpsucr
    syl3anc
    ex
end
