include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "ltadd1d.mm"
include "mpbid.mm"

theorem ltadd1dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume ltadd1dd.4: |- ( ph -> A < B )


  assert |- ( ph -> ( A + C ) < ( B + C ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cA
    cC
    caddc
    co
    cB
    cC
    caddc
    co
    clt
    wbr
    ltadd1dd.4
    wph
    cA
    cB
    cC
    leidd.1
    ltnegd.2
    ltadd1d.3
    ltadd1d
    mpbid
end
