include "wss.mm"
include "cun.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "syl2anc.mm"

theorem unssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume unssd.1: |- ( ph -> A C_ C )
  assume unssd.2: |- ( ph -> B C_ C )


  assert |- ( ph -> ( A u. B ) C_ C )

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
    cA
    cB
    cun
    cC
    wss
    #
    unssd.1
    unssd.2
    @0
    @1
    wa
    @2
    cA
    cB
    cC
    unss
    biimpi
    syl2anc
end
