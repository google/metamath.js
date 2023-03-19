include "cr.mm"
include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cmpt.mm"
include "cn0.mm"
include "cexp.mm"
include "c3.mm"
include "cmul.mm"
include "csu.mm"
include "eqid.mm"
include "cnndvlem2.mm"

theorem cnndv
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- E. f ( f e. ( RR -cn-> RR ) /\ dom ( RR _D f ) = (/) )

  proof
    vx
    vy
    vw
    vx
    cr
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    cfl
    cfv
    @0
    cmin
    co
    cabs
    cfv
    cmpt
    #
    vf
    vi
    vn
    vy
    cr
    vn
    cn0
    @1
    vn
    cv
    #
    cexp
    co
    c2
    c3
    cmul
    co
    @3
    cexp
    co
    vy
    cv
    cmul
    co
    @2
    cfv
    cmul
    co
    cmpt
    cmpt
    #
    vw
    cr
    cn0
    vi
    cv
    vw
    cv
    @4
    cfv
    cfv
    vi
    csu
    cmpt
    #
    @2
    eqid
    @4
    eqid
    @5
    eqid
    cnndvlem2
end
