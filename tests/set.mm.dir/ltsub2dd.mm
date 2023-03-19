include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "ltsub2d.mm"
include "mpbid.mm"

theorem ltsub2dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume ltadd1dd.4: |- ( ph -> A < B )


  assert |- ( ph -> ( C - B ) < ( C - A ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cC
    cB
    cmin
    co
    cC
    cA
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
    ltsub2d
    mpbid
end
