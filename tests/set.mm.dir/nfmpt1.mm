include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "nfopab1.mm"
include "nfcxfr.mm"

theorem nfmpt1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vz: setvar z


  assert |- F/_ x ( x e. A |-> B )

  proof
    vx
    vx
    cA
    cB
    cmpt
    vx
    cv
    cA
    wcel
    vz
    cv
    cB
    wceq
    wa
    #
    vx
    vz
    copab
    vx
    vz
    cA
    cB
    df-mpt
    @0
    vx
    vz
    nfopab1
    nfcxfr
end
