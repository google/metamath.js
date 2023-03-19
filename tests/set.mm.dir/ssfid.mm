include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem ssfid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ssfid.1: |- ( ph -> A e. Fin )
  assume ssfid.2: |- ( ph -> B C_ A )


  assert |- ( ph -> B e. Fin )

  proof
    wph
    cA
    cfn
    wcel
    cB
    cA
    wss
    cB
    cfn
    wcel
    ssfid.1
    ssfid.2
    cA
    cB
    ssfi
    syl2anc
end
