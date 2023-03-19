include "cmul.mm"
include "co.mm"
include "recnd.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem int-mulassocd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-mulassocd.1: |- ( ph -> B e. RR )
  assume int-mulassocd.2: |- ( ph -> C e. RR )
  assume int-mulassocd.3: |- ( ph -> D e. RR )
  assume int-mulassocd.4: |- ( ph -> A = B )


  assert |- ( ph -> ( B x. ( C x. D ) ) = ( ( A x. C ) x. D ) )

  proof
    wph
    cB
    cC
    cmul
    co
    #
    cD
    cmul
    co
    cB
    cC
    cD
    cmul
    co
    cmul
    co
    cA
    cC
    cmul
    co
    #
    cD
    cmul
    co
    wph
    cB
    cC
    cD
    wph
    cB
    int-mulassocd.1
    recnd
    wph
    cC
    int-mulassocd.2
    recnd
    wph
    cD
    int-mulassocd.3
    recnd
    mulassd
    wph
    @0
    @1
    cD
    cmul
    wph
    cB
    cA
    cC
    cmul
    wph
    cA
    cB
    int-mulassocd.4
    eqcomd
    oveq1d
    oveq1d
    eqtr3d
end
