include "wss.mm"
include "wa.mm"
include "cin.mm"
include "jca.mm"
include "ssin.mm"
include "sylib.mm"

theorem ssind
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssind.1: |- ( ph -> A C_ B )
  assume ssind.2: |- ( ph -> A C_ C )


  assert |- ( ph -> A C_ ( B i^i C ) )

  proof
    wph
    cA
    cB
    wss
    #
    cA
    cC
    wss
    #
    wa
    cA
    cB
    cC
    cin
    wss
    wph
    @0
    @1
    ssind.1
    ssind.2
    jca
    cA
    cB
    cC
    ssin
    sylib
end
