include "crli.mm"
include "wbr.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "rlimpm.mm"
include "wf.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2.mm"
include "simprbi.mm"
include "syl.mm"

theorem rlimss
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k


  assert |- ( F ~~>r A -> dom F C_ RR )

  proof
    cF
    cA
    crli
    wbr
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
    cA
    cF
    rlimpm
    @0
    @1
    cc
    cF
    wf
    @2
    cc
    cr
    cF
    cnex
    reex
    elpm2
    simprbi
    syl
end
