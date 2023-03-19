include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "ltmul1d.mm"
include "mpbid.mm"

theorem ltmul1dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )
  assume ltdiv1dd.4: |- ( ph -> A < B )


  assert |- ( ph -> ( A x. C ) < ( B x. C ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cA
    cC
    cmul
    co
    cB
    cC
    cmul
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
    ltmul1d
    mpbid
end
