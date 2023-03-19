include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "adddird.mm"
include "eqtrd.mm"

theorem joinlmuladdmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume joinlmuladdmuld.1: |- ( ph -> A e. CC )
  assume joinlmuladdmuld.2: |- ( ph -> B e. CC )
  assume joinlmuladdmuld.3: |- ( ph -> C e. CC )
  assume joinlmuladdmuld.4: |- ( ph -> ( ( A x. B ) + ( C x. B ) ) = D )


  assert |- ( ph -> ( ( A + C ) x. B ) = D )

  proof
    wph
    cA
    cC
    caddc
    co
    cB
    cmul
    co
    cA
    cB
    cmul
    co
    cC
    cB
    cmul
    co
    caddc
    co
    cD
    wph
    cA
    cC
    cB
    joinlmuladdmuld.1
    joinlmuladdmuld.3
    joinlmuladdmuld.2
    adddird
    joinlmuladdmuld.4
    eqtrd
end
