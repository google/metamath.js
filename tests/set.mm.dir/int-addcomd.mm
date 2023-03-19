include "caddc.mm"
include "co.mm"
include "recnd.mm"
include "addcomd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem int-addcomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume int-addcomd.1: |- ( ph -> B e. RR )
  assume int-addcomd.2: |- ( ph -> C e. RR )
  assume int-addcomd.3: |- ( ph -> A = B )


  assert |- ( ph -> ( B + C ) = ( C + A ) )

  proof
    wph
    cB
    cC
    caddc
    co
    cC
    cB
    caddc
    co
    cC
    cA
    caddc
    co
    wph
    cB
    cC
    wph
    cB
    int-addcomd.1
    recnd
    wph
    cC
    int-addcomd.2
    recnd
    addcomd
    wph
    cB
    cA
    cC
    caddc
    wph
    cA
    cB
    int-addcomd.3
    eqcomd
    oveq2d
    eqtrd
end
