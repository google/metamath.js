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
include "relexpsucl.mm"
include "syl3anc.mm"
include "ex.mm"

theorem relexpsucld
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexpsucld.1: |- ( ph -> Rel R )
  assume relexpsucld.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> ( R ^r ( N + 1 ) ) = ( R o. ( R ^r N ) ) ) )

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
    cR
    cN
    crelexp
    co
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
    relexpsucld.2
    adantr
    wph
    @3
    @0
    relexpsucld.1
    adantr
    wph
    @0
    simpr
    cR
    cN
    cvv
    relexpsucl
    syl3anc
    ex
end
