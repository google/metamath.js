include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "ltsub1d.mm"
include "mpbid.mm"

theorem ltsub1dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume ltadd1dd.4: |- ( ph -> A < B )


  assert |- ( ph -> ( A - C ) < ( B - C ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cA
    cC
    cmin
    co
    cB
    cC
    cmin
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
    ltsub1d
    mpbid
end
