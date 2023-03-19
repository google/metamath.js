include "crli.mm"
include "wbr.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "rlimpm.mm"
include "wss.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2.mm"
include "simplbi.mm"
include "syl.mm"

theorem rlimf
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k


  assert |- ( F ~~>r A -> F : dom F --> CC )

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
    cc
    cF
    wf
    #
    cA
    cF
    rlimpm
    @0
    @2
    @1
    cr
    wss
    cc
    cr
    cF
    cnex
    reex
    elpm2
    simplbi
    syl
end
