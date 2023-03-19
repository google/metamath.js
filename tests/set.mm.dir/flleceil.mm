include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cceil.mm"
include "reflcl.mm"
include "id.mm"
include "ceilcl.mm"
include "zred.mm"
include "flle.mm"
include "ceilge.mm"
include "letrd.mm"

theorem flleceil
  let cA: class A


  assert |- ( A e. RR -> ( |_ ` A ) <_ ( |^ ` A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    cA
    cA
    cceil
    cfv
    #
    cA
    reflcl
    @0
    id
    @0
    @1
    cA
    ceilcl
    zred
    cA
    flle
    cA
    ceilge
    letrd
end
