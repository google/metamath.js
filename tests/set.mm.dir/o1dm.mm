include "co1.mm"
include "wcel.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "elo1.mm"
include "simplbi.mm"
include "wf.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2.mm"
include "simprbi.mm"
include "syl.mm"

theorem o1dm
  let cF: class F
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let vf: setvar f
  let cM: class M


  assert |- ( F e. O(1) -> dom F C_ RR )

  proof
    cF
    co1
    wcel
    #
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    cF
    cdm
    #
    cr
    wss
    #
    @0
    @1
    vy
    cv
    cF
    cfv
    cabs
    cfv
    vm
    cv
    cle
    wbr
    vy
    @2
    vx
    cv
    cpnf
    cico
    co
    cin
    wral
    vm
    cr
    wrex
    vx
    cr
    wrex
    vx
    vy
    vm
    cF
    elo1
    simplbi
    @1
    @2
    cc
    cF
    wf
    @3
    cc
    cr
    cF
    cnex
    reex
    elpm2
    simprbi
    syl
end
