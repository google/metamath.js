include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "ltdiv1d.mm"
include "mpbid.mm"

theorem ltdiv1dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )
  assume ltdiv1dd.4: |- ( ph -> A < B )


  assert |- ( ph -> ( A / C ) < ( B / C ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    clt
    wbr
    ltdiv1dd.4
    wph
    cA
    cB
    cC
    ltmul1d.1
    ltmul1d.2
    ltmul1d.3
    ltdiv1d
    mpbid
end
