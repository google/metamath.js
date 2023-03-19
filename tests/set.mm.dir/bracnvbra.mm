include "chil.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "cbr.mm"
include "wf1o.mm"
include "wcel.mm"
include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "bra11.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"

theorem bracnvbra
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U


  assert |- ( T e. ( LinFn i^i ContFn ) -> ( bra ` ( `' bra ` T ) ) = T )

  proof
    chil
    clf
    ccnfn
    cin
    #
    cbr
    wf1o
    cT
    @0
    wcel
    cT
    cbr
    ccnv
    cfv
    cbr
    cfv
    cT
    wceq
    bra11
    chil
    @0
    cT
    cbr
    f1ocnvfv2
    mpan
end
