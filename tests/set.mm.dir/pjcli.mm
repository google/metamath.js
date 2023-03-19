include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "axpjcl.mm"
include "mpan.mm"

theorem pjcli
  let cA: class A
  let cH: class H
  assume pjcl.1: |- H e. CH


  assert |- ( A e. ~H -> ( ( projh ` H ) ` A ) e. H )

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
    cH
    wcel
    pjcl.1
    cA
    cH
    axpjcl
    mpan
end
