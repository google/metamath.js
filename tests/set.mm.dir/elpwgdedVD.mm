include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cpw.mm"
include "elpwg.mm"
include "biimpar.mm"
include "el12.mm"

theorem elpwgdedVD
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume elpwgdedVD.1: |- (. ph ->. A e. _V ).
  assume elpwgdedVD.2: |- (. ps ->. A C_ B ).


  assert |- (. (. ph ,. ps ). ->. A e. ~P B ).

  proof
    wph
    cA
    cvv
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cB
    cpw
    wcel
    #
    wps
    elpwgdedVD.1
    elpwgdedVD.2
    @0
    @2
    @1
    cA
    cB
    cvv
    elpwg
    biimpar
    el12
end
