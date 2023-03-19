include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cc.mm"
include "eqeltrd.mm"
include "diveq1ad.mm"
include "mpbird.mm"

theorem diveq1bd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume diveq1bd.1: |- ( ph -> B e. CC )
  assume diveq1bd.2: |- ( ph -> B =/= 0 )
  assume diveq1bd.3: |- ( ph -> A = B )


  assert |- ( ph -> ( A / B ) = 1 )

  proof
    wph
    cA
    cB
    cdiv
    co
    c1
    wceq
    cA
    cB
    wceq
    diveq1bd.3
    wph
    cA
    cB
    wph
    cA
    cB
    cc
    diveq1bd.3
    diveq1bd.1
    eqeltrd
    diveq1bd.1
    diveq1bd.2
    diveq1ad
    mpbird
end
