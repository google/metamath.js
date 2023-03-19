include "ctmd.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "simpl.mm"
include "ctopon.mm"
include "cfv.mm"
include "tmdtopon.mm"
include "adantr.mm"
include "simpr.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1plusg.mm"
include "syl5eqel.mm"

theorem tmdlactcn
  let vx: setvar x
  let cA: class A
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vg: setvar g
  assume tgplacthmeo.1: |- F = ( x e. X |-> ( A .+ x ) )
  assume tgplacthmeo.2: |- X = ( Base ` G )
  assume tgplacthmeo.3: |- .+ = ( +g ` G )
  assume tgplacthmeo.4: |- J = ( TopOpen ` G )

  disjoint A x
  disjoint G x
  disjoint J x
  disjoint .+ x
  disjoint X x
  disjoint g x
  disjoint A g
  disjoint G g
  disjoint .+ g
  disjoint X g
  assert |- ( ( G e. TopMnd /\ A e. X ) -> F e. ( J Cn J ) )

  proof
    cG
    ctmd
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cF
    vx
    cX
    cA
    vx
    cv
    #
    c.pl
    co
    cmpt
    cJ
    cJ
    ccn
    co
    tgplacthmeo.1
    @2
    vx
    cA
    @3
    c.pl
    cG
    cJ
    cJ
    cX
    tgplacthmeo.4
    tgplacthmeo.3
    @0
    @1
    simpl
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @1
    cG
    cJ
    cX
    tgplacthmeo.4
    tgplacthmeo.2
    tmdtopon
    adantr
    #
    @2
    vx
    cA
    cJ
    cJ
    cX
    cX
    @4
    @4
    @0
    @1
    simpr
    cnmptc
    @2
    vx
    cJ
    cX
    @4
    cnmptid
    cnmpt1plusg
    syl5eqel
end
