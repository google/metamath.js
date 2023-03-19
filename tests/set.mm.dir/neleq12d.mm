include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "eleq12d.mm"
include "notbid.mm"
include "df-nel.mm"
include "3bitr4g.mm"

theorem neleq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume neleq12d.1: |- ( ph -> A = B )
  assume neleq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A e/ C <-> B e/ D ) )

  proof
    wph
    cA
    cC
    wcel
    #
    wn
    cB
    cD
    wcel
    #
    wn
    cA
    cC
    wnel
    cB
    cD
    wnel
    wph
    @0
    @1
    wph
    cA
    cB
    cC
    cD
    neleq12d.1
    neleq12d.2
    eleq12d
    notbid
    cA
    cC
    df-nel
    cB
    cD
    df-nel
    3bitr4g
end
