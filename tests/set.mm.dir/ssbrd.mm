include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "sseld.mm"
include "df-br.mm"
include "3imtr4g.mm"

theorem ssbrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ssbrd.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( C A D -> C B D ) )

  proof
    wph
    cC
    cD
    cop
    #
    cA
    wcel
    @0
    cB
    wcel
    cC
    cD
    cA
    wbr
    cC
    cD
    cB
    wbr
    wph
    cA
    cB
    @0
    ssbrd.1
    sseld
    cC
    cD
    cA
    df-br
    cC
    cD
    cB
    df-br
    3imtr4g
end
