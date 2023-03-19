include "cmin.mm"
include "co.mm"
include "wne.mm"
include "subcan2ad.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem subneintr2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume subneintr2d.4: |- ( ph -> A =/= B )


  assert |- ( ph -> ( A - C ) =/= ( B - C ) )

  proof
    wph
    cA
    cC
    cmin
    co
    #
    cB
    cC
    cmin
    co
    #
    wne
    cA
    cB
    wne
    subneintr2d.4
    wph
    @0
    @1
    cA
    cB
    wph
    cA
    cB
    cC
    negidd.1
    pncand.2
    subaddd.3
    subcan2ad
    necon3bid
    mpbird
end
