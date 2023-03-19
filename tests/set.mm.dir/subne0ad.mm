include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "subeq0ad.mm"
include "necon3bid.mm"
include "mpbid.mm"

theorem subne0ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subne0ad.3: |- ( ph -> ( A - B ) =/= 0 )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cc0
    wne
    cA
    cB
    wne
    subne0ad.3
    wph
    @0
    cc0
    cA
    cB
    wph
    cA
    cB
    negidd.1
    pncand.2
    subeq0ad
    necon3bid
    mpbid
end
