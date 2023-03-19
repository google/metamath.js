include "cmin.mm"
include "co.mm"
include "subcli.mm"
include "cmul.mm"
include "mulcli.mm"
include "caddc.mm"
include "eqtr3i.mm"
include "mvlraddi.mm"
include "assraddsubi.mm"
include "mvrladdi.mm"
include "joinlmulsubmuli.mm"
include "mvllmuli.mm"

theorem i2linesi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume i2linesi.1: |- A e. CC
  assume i2linesi.2: |- B e. CC
  assume i2linesi.3: |- C e. CC
  assume i2linesi.4: |- D e. CC
  assume i2linesi.5: |- X e. CC
  assume i2linesi.6: |- Y = ( ( A x. X ) + B )
  assume i2linesi.7: |- Y = ( ( C x. X ) + D )
  assume i2linesi.8: |- ( A - C ) =/= 0


  assert |- X = ( ( D - B ) / ( A - C ) )

  proof
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
    cA
    cC
    i2linesi.1
    i2linesi.3
    subcli
    i2linesi.5
    i2linesi.8
    cA
    cX
    cC
    @0
    i2linesi.1
    i2linesi.5
    i2linesi.3
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
    cC
    cX
    i2linesi.3
    i2linesi.5
    mulcli
    #
    cD
    cB
    i2linesi.4
    i2linesi.2
    subcli
    @1
    @2
    cD
    cB
    @3
    i2linesi.4
    i2linesi.2
    @1
    cB
    @2
    cD
    caddc
    co
    #
    cA
    cX
    i2linesi.1
    i2linesi.5
    mulcli
    i2linesi.2
    cY
    @1
    cB
    caddc
    co
    @4
    i2linesi.6
    i2linesi.7
    eqtr3i
    mvlraddi
    assraddsubi
    mvrladdi
    joinlmulsubmuli
    mvllmuli
end
