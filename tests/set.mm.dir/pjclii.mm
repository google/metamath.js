include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "pjcli.mm"
include "ax-mp.mm"

theorem pjclii
  let cA: class A
  let cH: class H
  assume pjcli.1: |- H e. CH
  assume pjcli.2: |- A e. ~H


  assert |- ( ( projh ` H ) ` A ) e. H

  proof
    cA
    chil
    wcel
    cA
    cH
    cpjh
    cfv
    cfv
    cH
    wcel
    pjcli.2
    cA
    cH
    pjcli.1
    pjcli
    ax-mp
end
