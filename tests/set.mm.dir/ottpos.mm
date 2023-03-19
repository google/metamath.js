include "wcel.mm"
include "cop.mm"
include "ctpos.mm"
include "cotp.mm"
include "wbr.mm"
include "brtpos.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "df-ot.mm"
include "eleq1i.mm"
include "3bitr4g.mm"

theorem ottpos
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( C e. V -> ( <. A , B , C >. e. tpos F <-> <. B , A , C >. e. F ) )

  proof
    cC
    cV
    wcel
    #
    cA
    cB
    cop
    #
    cC
    cop
    #
    cF
    ctpos
    #
    wcel
    #
    cB
    cA
    cop
    #
    cC
    cop
    #
    cF
    wcel
    #
    cA
    cB
    cC
    cotp
    #
    @3
    wcel
    cB
    cA
    cC
    cotp
    #
    cF
    wcel
    @0
    @1
    cC
    @3
    wbr
    @5
    cC
    cF
    wbr
    @4
    @7
    cA
    cB
    cC
    cF
    cV
    brtpos
    @1
    cC
    @3
    df-br
    @5
    cC
    cF
    df-br
    3bitr3g
    @8
    @2
    @3
    cA
    cB
    cC
    df-ot
    eleq1i
    @9
    @6
    cF
    cB
    cA
    cC
    df-ot
    eleq1i
    3bitr4g
end
