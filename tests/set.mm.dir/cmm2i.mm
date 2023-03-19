include "cin.mm"
include "ccm.mm"
include "cmm1i.mm"
include "incom.mm"
include "breqtri.mm"

theorem cmm2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- B C_H ( A i^i B )

  proof
    cB
    cB
    cA
    cin
    cA
    cB
    cin
    ccm
    cB
    cA
    pjoml2.2
    pjoml2.1
    cmm1i
    cB
    cA
    incom
    breqtri
end
