include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addcan2d.mm"
include "mpbid.mm"

theorem addcan2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )
  assume addcan2ad.4: |- ( ph -> ( A + C ) = ( B + C ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cC
    caddc
    co
    cB
    cC
    caddc
    co
    wceq
    cA
    cB
    wceq
    addcan2ad.4
    wph
    cA
    cB
    cC
    muld.1
    addcomd.2
    addcand.3
    addcan2d
    mpbid
end
