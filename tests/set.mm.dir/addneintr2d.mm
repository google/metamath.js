include "caddc.mm"
include "co.mm"
include "wne.mm"
include "addcan2d.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem addneintr2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )
  assume addneintr2d.4: |- ( ph -> A =/= B )


  assert |- ( ph -> ( A + C ) =/= ( B + C ) )

  proof
    wph
    cA
    cC
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    wne
    cA
    cB
    wne
    addneintr2d.4
    wph
    @0
    @1
    cA
    cB
    wph
    cA
    cB
    cC
    muld.1
    addcomd.2
    addcand.3
    addcan2d
    necon3bid
    mpbird
end
