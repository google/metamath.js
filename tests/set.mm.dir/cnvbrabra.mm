include "chil.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "cbr.mm"
include "wf1o.mm"
include "wcel.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "bra11.mm"
include "f1ocnvfv1.mm"
include "mpan.mm"

theorem cnvbrabra
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( A e. ~H -> ( `' bra ` ( bra ` A ) ) = A )

  proof
    chil
    clf
    ccnfn
    cin
    #
    cbr
    wf1o
    cA
    chil
    wcel
    cA
    cbr
    cfv
    cbr
    ccnv
    cfv
    cA
    wceq
    bra11
    chil
    @0
    cA
    cbr
    f1ocnvfv1
    mpan
end
