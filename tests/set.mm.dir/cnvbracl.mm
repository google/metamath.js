include "chil.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "cbr.mm"
include "wf1o.mm"
include "wcel.mm"
include "ccnv.mm"
include "cfv.mm"
include "bra11.mm"
include "f1ocnvdm.mm"
include "mpan.mm"

theorem cnvbracl
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


  assert |- ( T e. ( LinFn i^i ContFn ) -> ( `' bra ` T ) e. ~H )

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
    chil
    wcel
    bra11
    chil
    @0
    cT
    cbr
    f1ocnvdm
    mpan
end
