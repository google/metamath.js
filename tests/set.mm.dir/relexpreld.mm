include "cvv.mm"
include "wcel.mm"
include "wrel.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "wi.mm"
include "relexprel.mm"
include "3coml.mm"
include "3exp.mm"
include "sylc.mm"

theorem relexpreld
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexpreld.1: |- ( ph -> Rel R )
  assume relexpreld.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> Rel ( R ^r N ) ) )

  proof
    wph
    cR
    cvv
    wcel
    #
    cR
    wrel
    #
    cN
    cn0
    wcel
    #
    cR
    cN
    crelexp
    co
    wrel
    #
    wi
    relexpreld.2
    relexpreld.1
    @0
    @1
    @2
    @3
    @2
    @0
    @1
    @3
    cR
    cN
    cvv
    relexprel
    3coml
    3exp
    sylc
end
