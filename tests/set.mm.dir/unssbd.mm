include "wss.mm"
include "cun.mm"
include "wa.mm"
include "unss.mm"
include "sylibr.mm"
include "simprd.mm"

theorem unssbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume unssad.1: |- ( ph -> ( A u. B ) C_ C )


  assert |- ( ph -> B C_ C )

  proof
    wph
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wph
    cA
    cB
    cun
    cC
    wss
    @0
    @1
    wa
    unssad.1
    cA
    cB
    cC
    unss
    sylibr
    simprd
end
