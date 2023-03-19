include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "recnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "eqcomd.mm"

theorem int-eqmvtd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-eqmvtd.1: |- ( ph -> C e. RR )
  assume int-eqmvtd.2: |- ( ph -> D e. RR )
  assume int-eqmvtd.3: |- ( ph -> A = B )
  assume int-eqmvtd.4: |- ( ph -> A = ( C + D ) )


  assert |- ( ph -> C = ( B - D ) )

  proof
    wph
    cB
    cD
    cmin
    co
    #
    cC
    wph
    @0
    cC
    cD
    caddc
    co
    #
    cD
    cmin
    co
    cC
    wph
    cB
    @1
    cD
    cmin
    wph
    cA
    cB
    @1
    int-eqmvtd.3
    int-eqmvtd.4
    eqtr3d
    oveq1d
    wph
    cC
    cD
    wph
    cC
    int-eqmvtd.1
    recnd
    wph
    cD
    int-eqmvtd.2
    recnd
    pncand
    eqtrd
    eqcomd
end
