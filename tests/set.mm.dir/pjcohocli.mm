include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "pjfi.mm"
include "hocoi.mm"
include "ffvelrni.mm"
include "pjcli.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem pjcohocli
  let cA: class A
  let cT: class T
  let cH: class H
  assume pjcohocl.1: |- H e. CH
  assume pjcohocl.2: |- T : ~H --> ~H


  assert |- ( A e. ~H -> ( ( ( projh ` H ) o. T ) ` A ) e. H )

  proof
    cA
    chil
    wcel
    #
    cA
    cH
    cpjh
    cfv
    #
    cT
    ccom
    cfv
    cA
    cT
    cfv
    #
    @1
    cfv
    #
    cH
    cA
    @1
    cT
    cH
    pjcohocl.1
    pjfi
    pjcohocl.2
    hocoi
    @0
    @2
    chil
    wcel
    @3
    cH
    wcel
    chil
    chil
    cA
    cT
    pjcohocl.2
    ffvelrni
    @2
    cH
    pjcohocl.1
    pjcli
    syl
    eqeltrd
end
