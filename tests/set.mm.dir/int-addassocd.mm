include "caddc.mm"
include "co.mm"
include "recnd.mm"
include "addassd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"

theorem int-addassocd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-addassocd.1: |- ( ph -> A e. RR )
  assume int-addassocd.2: |- ( ph -> C e. RR )
  assume int-addassocd.3: |- ( ph -> D e. RR )
  assume int-addassocd.4: |- ( ph -> A = B )


  assert |- ( ph -> ( B + ( C + D ) ) = ( ( A + C ) + D ) )

  proof
    wph
    cA
    cC
    caddc
    co
    cD
    caddc
    co
    cA
    cC
    cD
    caddc
    co
    #
    caddc
    co
    cB
    @0
    caddc
    co
    wph
    cA
    cC
    cD
    wph
    cA
    int-addassocd.1
    recnd
    wph
    cC
    int-addassocd.2
    recnd
    wph
    cD
    int-addassocd.3
    recnd
    addassd
    wph
    cA
    cB
    @0
    caddc
    int-addassocd.4
    oveq1d
    eqtr2d
end
