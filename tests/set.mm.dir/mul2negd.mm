include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul2neg.mm"
include "syl2anc.mm"

theorem mul2negd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mulm1d.1: |- ( ph -> A e. CC )
  assume mulnegd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( -u A x. -u B ) = ( A x. B ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cneg
    cB
    cneg
    cmul
    co
    cA
    cB
    cmul
    co
    wceq
    mulm1d.1
    mulnegd.2
    cA
    cB
    mul2neg
    syl2anc
end
