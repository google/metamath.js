include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "lediv1d.mm"
include "mpbid.mm"

theorem lediv1dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )
  assume lediv1dd.4: |- ( ph -> A <_ B )


  assert |- ( ph -> ( A / C ) <_ ( B / C ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    cle
    wbr
    lediv1dd.4
    wph
    cA
    cB
    cC
    ltmul1d.1
    ltmul1d.2
    ltmul1d.3
    lediv1d
    mpbid
end
