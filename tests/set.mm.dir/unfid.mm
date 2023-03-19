include "cfn.mm"
include "wcel.mm"
include "cun.mm"
include "unfi.mm"
include "syl2anc.mm"

theorem unfid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume unfid.1: |- ( ph -> A e. Fin )
  assume unfid.2: |- ( ph -> B e. Fin )


  assert |- ( ph -> ( A u. B ) e. Fin )

  proof
    wph
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    cA
    cB
    cun
    cfn
    wcel
    unfid.1
    unfid.2
    cA
    cB
    unfi
    syl2anc
end
