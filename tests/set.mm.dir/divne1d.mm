include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wne.mm"
include "diveq1ad.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem divne1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )
  assume divne1d.4: |- ( ph -> A =/= B )


  assert |- ( ph -> ( A / B ) =/= 1 )

  proof
    wph
    cA
    cB
    cdiv
    co
    #
    c1
    wne
    cA
    cB
    wne
    divne1d.4
    wph
    @0
    c1
    cA
    cB
    wph
    cA
    cB
    div1d.1
    divcld.2
    divcld.3
    diveq1ad
    necon3bid
    mpbird
end
