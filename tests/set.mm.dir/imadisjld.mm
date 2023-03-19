include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cima.mm"
include "imadisj.mm"
include "sylibr.mm"

theorem imadisjld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume imadisjld.1: |- ( ph -> ( dom A i^i B ) = (/) )


  assert |- ( ph -> ( A " B ) = (/) )

  proof
    wph
    cA
    cdm
    cB
    cin
    c0
    wceq
    cA
    cB
    cima
    c0
    wceq
    imadisjld.1
    cA
    cB
    imadisj
    sylibr
end
