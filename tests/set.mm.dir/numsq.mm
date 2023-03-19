include "cq.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cnumer.mm"
include "cfv.mm"
include "wceq.mm"
include "cdenom.mm"
include "numdensq.mm"
include "simpld.mm"

theorem numsq
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( numer ` ( A ^ 2 ) ) = ( ( numer ` A ) ^ 2 ) )

  proof
    cA
    cq
    wcel
    cA
    c2
    cexp
    co
    #
    cnumer
    cfv
    cA
    cnumer
    cfv
    c2
    cexp
    co
    wceq
    @0
    cdenom
    cfv
    cA
    cdenom
    cfv
    c2
    cexp
    co
    wceq
    cA
    numdensq
    simpld
end
