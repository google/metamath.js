include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "pjhcl.mm"
include "mpan.mm"

theorem pjhcli
  let cA: class A
  let cH: class H
  assume pjcl.1: |- H e. CH


  assert |- ( A e. ~H -> ( ( projh ` H ) ` A ) e. ~H )

  proof
    cH
    cch
    wcel
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
    pjcl.1
    cA
    cH
    pjhcl
    mpan
end
