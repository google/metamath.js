include "cvv.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wrel.mm"
include "wi.mm"
include "wa.mm"
include "cn0.mm"
include "crelexp.mm"
include "ccom.mm"
include "a1d.mm"
include "jca.mm"
include "relexpaddg.mm"
include "3exp2.mm"
include "imp4b.mm"
include "syl5com.mm"

theorem relexpaddd
  let wph: wff ph
  let cR: class R
  let cM: class M
  let cN: class N
  assume relexpaddd.1: |- ( ph -> Rel R )
  assume relexpaddd.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( ( N e. NN0 /\ M e. NN0 ) -> ( ( R ^r N ) o. ( R ^r M ) ) = ( R ^r ( N + M ) ) ) )

  proof
    wph
    cR
    cvv
    wcel
    #
    cN
    cM
    caddc
    co
    #
    c1
    wceq
    #
    cR
    wrel
    #
    wi
    #
    wa
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    cR
    cN
    crelexp
    co
    cR
    cM
    crelexp
    co
    ccom
    cR
    @1
    crelexp
    co
    wceq
    #
    wph
    @0
    @4
    relexpaddd.2
    wph
    @3
    @2
    relexpaddd.1
    a1d
    jca
    @5
    @6
    @0
    @4
    @7
    @5
    @6
    @0
    @4
    @7
    cR
    cM
    cN
    cvv
    relexpaddg
    3exp2
    imp4b
    syl5com
end
