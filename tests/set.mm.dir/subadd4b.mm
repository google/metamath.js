include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subadd4d.mm"
include "subcld.mm"
include "subsub2d.mm"
include "addcomd.mm"
include "oveq2d.mm"
include "addsub4d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem subadd4b
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume subadd4b.1: |- ( ph -> A e. CC )
  assume subadd4b.2: |- ( ph -> B e. CC )
  assume subadd4b.3: |- ( ph -> C e. CC )
  assume subadd4b.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A - B ) + ( C - D ) ) = ( ( A - D ) + ( C - B ) ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cD
    cC
    cmin
    co
    cmin
    co
    cA
    cC
    caddc
    co
    #
    cB
    cD
    caddc
    co
    #
    cmin
    co
    #
    @0
    cC
    cD
    cmin
    co
    caddc
    co
    cA
    cD
    cmin
    co
    cC
    cB
    cmin
    co
    caddc
    co
    #
    wph
    cA
    cB
    cD
    cC
    subadd4b.1
    subadd4b.2
    subadd4b.4
    subadd4b.3
    subadd4d
    wph
    @0
    cD
    cC
    wph
    cA
    cB
    subadd4b.1
    subadd4b.2
    subcld
    subadd4b.4
    subadd4b.3
    subsub2d
    wph
    @3
    @1
    cD
    cB
    caddc
    co
    #
    cmin
    co
    @4
    wph
    @2
    @5
    @1
    cmin
    wph
    cB
    cD
    subadd4b.2
    subadd4b.4
    addcomd
    oveq2d
    wph
    cA
    cC
    cD
    cB
    subadd4b.1
    subadd4b.3
    subadd4b.4
    subadd4b.2
    addsub4d
    eqtrd
    3eqtr3d
end
