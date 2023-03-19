include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "pm3.2i.mm"
include "divdivdiv.mm"
include "mp4an.mm"

theorem divdivdivi
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
  assume divdivdiv.7: |- C =/= 0


  assert |- ( ( A / B ) / ( C / D ) ) = ( ( A x. D ) / ( B x. C ) )

  proof
    cA
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
    cC
    cc
    wcel
    #
    cC
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
    cdiv
    co
    cA
    cD
    cmul
    co
    cB
    cC
    cmul
    co
    cdiv
    co
    wceq
    divclz.1
    @0
    @1
    divclz.2
    divmuldiv.5
    pm3.2i
    @2
    @3
    divmulz.3
    divdivdiv.7
    pm3.2i
    @4
    @5
    divmuldiv.4
    divmuldiv.6
    pm3.2i
    cA
    cB
    cC
    cD
    divdivdiv
    mp4an
end
