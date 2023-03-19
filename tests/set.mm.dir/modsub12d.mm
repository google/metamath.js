include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmo.mm"
include "cmin.mm"
include "renegcld.mm"
include "modnegd.mm"
include "modadd12d.mm"
include "recnd.mm"
include "negsubd.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"

theorem modsub12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume modadd12d.1: |- ( ph -> A e. RR )
  assume modadd12d.2: |- ( ph -> B e. RR )
  assume modadd12d.3: |- ( ph -> C e. RR )
  assume modadd12d.4: |- ( ph -> D e. RR )
  assume modadd12d.5: |- ( ph -> E e. RR+ )
  assume modadd12d.6: |- ( ph -> ( A mod E ) = ( B mod E ) )
  assume modadd12d.7: |- ( ph -> ( C mod E ) = ( D mod E ) )


  assert |- ( ph -> ( ( A - C ) mod E ) = ( ( B - D ) mod E ) )

  proof
    wph
    cA
    cC
    cneg
    #
    caddc
    co
    #
    cE
    cmo
    co
    cB
    cD
    cneg
    #
    caddc
    co
    #
    cE
    cmo
    co
    cA
    cC
    cmin
    co
    #
    cE
    cmo
    co
    cB
    cD
    cmin
    co
    #
    cE
    cmo
    co
    wph
    cA
    cB
    @0
    @2
    cE
    modadd12d.1
    modadd12d.2
    wph
    cC
    modadd12d.3
    renegcld
    wph
    cD
    modadd12d.4
    renegcld
    modadd12d.5
    modadd12d.6
    wph
    cC
    cD
    cE
    modadd12d.3
    modadd12d.4
    modadd12d.5
    modadd12d.7
    modnegd
    modadd12d
    wph
    @1
    @4
    cE
    cmo
    wph
    cA
    cC
    wph
    cA
    modadd12d.1
    recnd
    wph
    cC
    modadd12d.3
    recnd
    negsubd
    oveq1d
    wph
    @3
    @5
    cE
    cmo
    wph
    cB
    cD
    wph
    cB
    modadd12d.2
    recnd
    wph
    cD
    modadd12d.4
    recnd
    negsubd
    oveq1d
    3eqtr3d
end
