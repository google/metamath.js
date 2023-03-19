include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addcand.mm"
include "mpbid.mm"

theorem addcanad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )
  assume addcanad.4: |- ( ph -> ( A + B ) = ( A + C ) )


  assert |- ( ph -> B = C )

  proof
    wph
    cA
    cB
    caddc
    co
    cA
    cC
    caddc
    co
    wceq
    cB
    cC
    wceq
    addcanad.4
    wph
    cA
    cB
    cC
    muld.1
    addcomd.2
    addcand.3
    addcand
    mpbid
end
