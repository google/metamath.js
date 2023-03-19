include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "con3d.mm"
include "df-nel.mm"
include "3imtr4g.mm"

theorem nelcon3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume nelcon3d.1: |- ( ph -> ( A e. B -> C e. D ) )


  assert |- ( ph -> ( C e/ D -> A e/ B ) )

  proof
    wph
    cC
    cD
    wcel
    #
    wn
    cA
    cB
    wcel
    #
    wn
    cC
    cD
    wnel
    cA
    cB
    wnel
    wph
    @1
    @0
    nelcon3d.1
    con3d
    cC
    cD
    df-nel
    cA
    cB
    df-nel
    3imtr4g
end
