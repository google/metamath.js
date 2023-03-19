include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "pm3.2i.mm"
include "divadddiv.mm"
include "mp4an.mm"

theorem divadddivi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divmuldiv.4: |- D e. CC
  assume divmuldiv.5: |- B =/= 0
  assume divmuldiv.6: |- D =/= 0


  assert |- ( ( A / B ) + ( C / D ) ) = ( ( ( A x. D ) + ( C x. B ) ) / ( B x. D ) )

  proof
    cA
    cc
    wcel
    cC
    cc
    wcel
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    cA
    cB
    cdiv
    co
    cC
    cD
    cdiv
    co
    caddc
    co
    cA
    cD
    cmul
    co
    cC
    cB
    cmul
    co
    caddc
    co
    cB
    cD
    cmul
    co
    cdiv
    co
    wceq
    divclz.1
    divmulz.3
    @0
    @1
    divclz.2
    divmuldiv.5
    pm3.2i
    @2
    @3
    divmuldiv.4
    divmuldiv.6
    pm3.2i
    cA
    cC
    cB
    cD
    divadddiv
    mp4an
end
