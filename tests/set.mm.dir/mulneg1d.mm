include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulneg1.mm"
include "syl2anc.mm"

theorem mulneg1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mulm1d.1: |- ( ph -> A e. CC )
  assume mulnegd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( -u A x. B ) = -u ( A x. B ) )

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
    cmul
    co
    cA
    cB
    cmul
    co
    cneg
    wceq
    mulm1d.1
    mulnegd.2
    cA
    cB
    mulneg1
    syl2anc
end
