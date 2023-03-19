include "cc.mm"
include "wss.mm"
include "ccpn.mm"
include "cfv.mm"
include "cn0.mm"
include "wfn.mm"
include "cv.mm"
include "cdvn.mm"
include "co.mm"
include "cdm.mm"
include "ccncf.mm"
include "wcel.mm"
include "cpm.mm"
include "crab.mm"
include "cmpt.mm"
include "ovex.mm"
include "rabex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "cpnfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem fncpn
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cF: class F
  let vm: setvar m
  let cM: class M
  let cN: class N
  let vs: setvar s


  assert |- ( S C_ CC -> ( C^n ` S ) Fn NN0 )

  proof
    cS
    cc
    wss
    #
    cS
    ccpn
    cfv
    #
    cn0
    wfn
    vn
    cn0
    vn
    cv
    cS
    vf
    cv
    #
    cdvn
    co
    cfv
    @2
    cdm
    cc
    ccncf
    co
    wcel
    #
    vf
    cc
    cS
    cpm
    co
    #
    crab
    #
    cmpt
    #
    cn0
    wfn
    vn
    cn0
    @5
    @6
    @3
    vf
    @4
    cc
    cS
    cpm
    ovex
    rabex
    @6
    eqid
    fnmpti
    @0
    cn0
    @1
    @6
    cS
    vf
    vn
    cpnfval
    fneq1d
    mpbiri
end
