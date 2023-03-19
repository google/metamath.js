include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wfo.mm"
include "f1ofo.mm"
include "fofi.mm"
include "ex.mm"
include "syl5.mm"
include "exlimdv.mm"
include "con3dimp.mm"

theorem fiinfnf1o
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint A f
  disjoint B f
  assert |- ( ( A e. Fin /\ -. B e. Fin ) -> -. E. f f : A -1-1-onto-> B )

  proof
    cA
    cfn
    wcel
    #
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    cB
    cfn
    wcel
    #
    @0
    @2
    @3
    vf
    @2
    cA
    cB
    @1
    wfo
    #
    @0
    @3
    cA
    cB
    @1
    f1ofo
    @0
    @4
    @3
    cA
    cB
    @1
    fofi
    ex
    syl5
    exlimdv
    con3dimp
end
