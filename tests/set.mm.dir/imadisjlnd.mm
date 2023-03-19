include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cima.mm"
include "wceq.mm"
include "imadisj.mm"
include "biimpi.mm"
include "necon3i.mm"
include "syl.mm"

theorem imadisjlnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume imadisjlnd.1: |- ( ph -> ( dom A i^i B ) =/= (/) )


  assert |- ( ph -> ( A " B ) =/= (/) )

  proof
    wph
    cA
    cdm
    cB
    cin
    #
    c0
    wne
    cA
    cB
    cima
    #
    c0
    wne
    imadisjlnd.1
    @1
    c0
    @0
    c0
    @1
    c0
    wceq
    @0
    c0
    wceq
    cA
    cB
    imadisj
    biimpi
    necon3i
    syl
end
