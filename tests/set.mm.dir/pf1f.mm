include "wcel.mm"
include "cpws.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "ccrg.mm"
include "cvv.mm"
include "eqid.mm"
include "pf1rcl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "csubrg.mm"
include "wss.mm"
include "pf1subrg.mm"
include "subrgss.mm"
include "3syl.mm"
include "id.mm"
include "sseldd.mm"
include "pwselbas.mm"

theorem pf1f
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  assume pf1rcl.q: |- Q = ran ( eval1 ` R )
  assume pf1f.b: |- B = ( Base ` R )


  assert |- ( F e. Q -> F : B --> B )

  proof
    cF
    cQ
    wcel
    #
    cB
    cR
    cB
    cR
    cB
    cpws
    co
    #
    cbs
    cfv
    #
    ccrg
    cF
    @1
    cvv
    @1
    eqid
    pf1f.b
    @2
    eqid
    #
    cQ
    cR
    cF
    pf1rcl.q
    pf1rcl
    #
    cB
    cvv
    wcel
    @0
    cB
    cR
    cbs
    cfv
    cvv
    pf1f.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    @0
    cQ
    @2
    cF
    @0
    cR
    ccrg
    wcel
    cQ
    @1
    csubrg
    cfv
    wcel
    cQ
    @2
    wss
    @4
    cB
    cQ
    cR
    pf1f.b
    pf1rcl.q
    pf1subrg
    cQ
    @2
    @1
    @3
    subrgss
    3syl
    @0
    id
    sseldd
    pwselbas
end
