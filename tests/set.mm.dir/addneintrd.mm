include "caddc.mm"
include "co.mm"
include "wne.mm"
include "addcand.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem addneintrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )
  assume addneintrd.4: |- ( ph -> B =/= C )


  assert |- ( ph -> ( A + B ) =/= ( A + C ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    wne
    cB
    cC
    wne
    addneintrd.4
    wph
    @0
    @1
    cB
    cC
    wph
    cA
    cB
    cC
    muld.1
    addcomd.2
    addcand.3
    addcand
    necon3bid
    mpbird
end
