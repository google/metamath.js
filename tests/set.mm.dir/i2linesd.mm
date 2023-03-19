include "cmin.mm"
include "co.mm"
include "subcld.mm"
include "cmul.mm"
include "mulcld.mm"
include "caddc.mm"
include "eqtr3d.mm"
include "mvlraddd.mm"
include "assraddsubd.mm"
include "mvrladdd.mm"
include "joinlmulsubmuld.mm"
include "mvllmuld.mm"

theorem i2linesd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume i2linesd.1: |- ( ph -> A e. CC )
  assume i2linesd.2: |- ( ph -> B e. CC )
  assume i2linesd.3: |- ( ph -> C e. CC )
  assume i2linesd.4: |- ( ph -> D e. CC )
  assume i2linesd.5: |- ( ph -> X e. CC )
  assume i2linesd.6: |- ( ph -> Y = ( ( A x. X ) + B ) )
  assume i2linesd.7: |- ( ph -> Y = ( ( C x. X ) + D ) )
  assume i2linesd.8: |- ( ph -> ( A - C ) =/= 0 )


  assert |- ( ph -> X = ( ( D - B ) / ( A - C ) ) )

  proof
    wph
    cA
    cC
    cmin
    co
    cX
    cD
    cB
    cmin
    co
    #
    wph
    cA
    cC
    i2linesd.1
    i2linesd.3
    subcld
    i2linesd.5
    i2linesd.8
    wph
    cA
    cX
    cC
    @0
    i2linesd.1
    i2linesd.5
    i2linesd.3
    wph
    cA
    cX
    cmul
    co
    #
    cC
    cX
    cmul
    co
    #
    @0
    wph
    cC
    cX
    i2linesd.3
    i2linesd.5
    mulcld
    #
    wph
    cD
    cB
    i2linesd.4
    i2linesd.2
    subcld
    wph
    @1
    @2
    cD
    cB
    @3
    i2linesd.4
    i2linesd.2
    wph
    @1
    cB
    @2
    cD
    caddc
    co
    #
    wph
    cA
    cX
    i2linesd.1
    i2linesd.5
    mulcld
    i2linesd.2
    wph
    cY
    @1
    cB
    caddc
    co
    @4
    i2linesd.6
    i2linesd.7
    eqtr3d
    mvlraddd
    assraddsubd
    mvrladdd
    joinlmulsubmuld
    mvllmuld
end
