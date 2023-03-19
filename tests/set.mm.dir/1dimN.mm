include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "2dim.mm"
include "r19.42v.mm"
include "simplbi.mm"
include "reximi.mm"
include "syl.mm"

theorem 1dimN
  let cA: class A
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume 2dim.j: |- .\/ = ( join ` K )
  assume 2dim.c: |- C = ( <o ` K )
  assume 2dim.a: |- A = ( Atoms ` K )

  disjoint A q
  disjoint .\/ q
  disjoint K q
  disjoint P q
  disjoint q r
  disjoint q s
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint .\/ r
  disjoint .\/ s
  disjoint K r
  disjoint K s
  disjoint P r
  disjoint P s
  disjoint C r
  assert |- ( ( K e. HL /\ P e. A ) -> E. q e. A P C ( P .\/ q ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    wa
    cP
    cP
    vq
    cv
    c.or
    co
    #
    cC
    wbr
    #
    @0
    @0
    vr
    cv
    c.or
    co
    cC
    wbr
    #
    wa
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    @1
    vq
    cA
    wrex
    cA
    cC
    cP
    c.or
    cK
    vr
    vq
    2dim.j
    2dim.c
    2dim.a
    2dim
    @3
    @1
    vq
    cA
    @3
    @1
    @2
    vr
    cA
    wrex
    @1
    @2
    vr
    cA
    r19.42v
    simplbi
    reximi
    syl
end
