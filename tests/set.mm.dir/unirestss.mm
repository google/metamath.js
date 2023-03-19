include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "restuni6.mm"
include "inss1.mm"
include "syl6eqss.mm"

theorem unirestss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume unirestss.1: |- ( ph -> A e. V )
  assume unirestss.2: |- ( ph -> B e. W )


  assert |- ( ph -> U. ( A |`t B ) C_ U. A )

  proof
    wph
    cA
    cB
    crest
    co
    cuni
    cA
    cuni
    #
    cB
    cin
    @0
    wph
    cA
    cB
    cV
    cW
    unirestss.1
    unirestss.2
    restuni6
    @0
    cB
    inss1
    syl6eqss
end
