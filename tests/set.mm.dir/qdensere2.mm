include "cq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccl.mm"
include "cr.mm"
include "tgioo.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "qdensere.mm"
include "eqtr3i.mm"

theorem qdensere2
  let cD: class D
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let cA: class A
  let cB: class B
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )
  assume tgioo.2: |- J = ( MetOpen ` D )


  assert |- ( ( cls ` J ) ` QQ ) = RR

  proof
    cq
    cioo
    crn
    ctg
    cfv
    #
    ccl
    cfv
    #
    cfv
    cq
    cJ
    ccl
    cfv
    #
    cfv
    cr
    cq
    @1
    @2
    @0
    cJ
    ccl
    cD
    cJ
    remet.1
    tgioo.2
    tgioo
    fveq2i
    fveq1i
    qdensere
    eqtr3i
end
