include "cioo.mm"
include "cq.mm"
include "cxp.mm"
include "cima.mm"
include "cr.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmpt2.mm"
include "crn.mm"
include "oveq1.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "eqid.mm"
include "mbfimaopnlem.mm"

theorem mbfimaopn
  let cA: class A
  let cF: class F
  let cJ: class J
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vw: setvar w
  let cK: class K
  let cG: class G
  assume mbfimaopn.1: |- J = ( TopOpen ` CCfld )


  assert |- ( ( F e. MblFn /\ A e. J ) -> ( `' F " A ) e. dom vol )

  proof
    vx
    vy
    cA
    cioo
    cq
    cq
    cxp
    cima
    #
    cF
    vt
    vw
    cr
    cr
    vt
    cv
    #
    ci
    vw
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt2
    cJ
    vx
    vy
    @0
    @0
    vx
    cv
    #
    vy
    cv
    #
    cxp
    cmpt2
    crn
    #
    mbfimaopn.1
    vt
    vw
    vx
    vy
    cr
    cr
    @4
    @5
    ci
    @6
    cmul
    co
    #
    caddc
    co
    @5
    @3
    caddc
    co
    @1
    @5
    @3
    caddc
    oveq1
    vw
    vy
    weq
    @3
    @8
    @5
    caddc
    @2
    @6
    ci
    cmul
    oveq2
    oveq2d
    cbvmpt2v
    @0
    eqid
    @7
    eqid
    mbfimaopnlem
end
