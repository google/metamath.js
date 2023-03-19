include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"

theorem iccssred
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume iccssred.1: |- ( ph -> A e. RR )
  assume iccssred.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A [,] B ) C_ RR )

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
    cicc
    co
    cr
    wss
    iccssred.1
    iccssred.2
    cA
    cB
    iccssre
    syl2anc
end
