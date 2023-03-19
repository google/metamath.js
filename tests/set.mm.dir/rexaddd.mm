include "cr.mm"
include "wcel.mm"
include "cxad.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "rexadd.mm"
include "syl2anc.mm"

theorem rexaddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rexaddd.1: |- ( ph -> A e. RR )
  assume rexaddd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A +e B ) = ( A + B ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cxad
    co
    cA
    cB
    caddc
    co
    wceq
    rexaddd.1
    rexaddd.2
    cA
    cB
    rexadd
    syl2anc
end
