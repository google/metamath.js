include "cid.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "imai.mm"
include "eqtr3i.mm"

theorem rnresi
  let cA: class A


  assert |- ran ( _I |` A ) = A

  proof
    cid
    cA
    cima
    cid
    cA
    cres
    crn
    cA
    cid
    cA
    df-ima
    cA
    imai
    eqtr3i
end
