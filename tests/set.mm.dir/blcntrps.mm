include "crp.mm"
include "wcel.mm"
include "cpsmet.mm"
include "cfv.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cbl.mm"
include "co.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "jca.mm"
include "xblcntrps.mm"
include "syl3an3.mm"

theorem blcntrps
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( D e. ( PsMet ` X ) /\ P e. X /\ R e. RR+ ) -> P e. ( P ( ball ` D ) R ) )

  proof
    cR
    crp
    wcel
    #
    cD
    cX
    cpsmet
    cfv
    wcel
    cP
    cX
    wcel
    cR
    cxr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    wa
    cP
    cP
    cR
    cD
    cbl
    cfv
    co
    wcel
    @0
    @1
    @2
    cR
    rpxr
    cR
    rpgt0
    jca
    cD
    cP
    cR
    cX
    xblcntrps
    syl3an3
end
