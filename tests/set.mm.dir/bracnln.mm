include "chil.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "cbr.mm"
include "wf1o.mm"
include "wf.mm"
include "bra11.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"

theorem bracnln
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


  assert |- ( A e. ~H -> ( bra ` A ) e. ( LinFn i^i ContFn ) )

  proof
    chil
    clf
    ccnfn
    cin
    #
    cA
    cbr
    chil
    @0
    cbr
    wf1o
    chil
    @0
    cbr
    wf
    bra11
    chil
    @0
    cbr
    f1of
    ax-mp
    ffvelrni
end
