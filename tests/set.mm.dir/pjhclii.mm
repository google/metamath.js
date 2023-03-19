include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "pjhcli.mm"
include "ax-mp.mm"

theorem pjhclii
  let cA: class A
  let cH: class H
  assume pjcli.1: |- H e. CH
  assume pjcli.2: |- A e. ~H


  assert |- ( ( projh ` H ) ` A ) e. ~H

  proof
    cA
    chil
    wcel
    cA
    cH
    cpjh
    cfv
    cfv
    chil
    wcel
    pjcli.2
    cA
    cH
    pjcli.1
    pjhcli
    ax-mp
end
