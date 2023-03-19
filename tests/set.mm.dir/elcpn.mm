include "cc.mm"
include "wss.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "ccpn.mm"
include "cfv.mm"
include "cv.mm"
include "cdvn.mm"
include "co.mm"
include "cdm.mm"
include "ccncf.mm"
include "cpm.mm"
include "crab.mm"
include "cmpt.mm"
include "cpnfval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "eqid.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "dmeq.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elcpn
  let cS: class S
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let vs: setvar s


  assert |- ( ( S C_ CC /\ N e. NN0 ) -> ( F e. ( ( C^n ` S ) ` N ) <-> ( F e. ( CC ^pm S ) /\ ( ( S Dn F ) ` N ) e. ( dom F -cn-> CC ) ) ) )

  proof
    cS
    cc
    wss
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cF
    cN
    cS
    ccpn
    cfv
    #
    cfv
    #
    wcel
    cF
    cN
    cS
    vf
    cv
    #
    cdvn
    co
    #
    cfv
    #
    @5
    cdm
    #
    cc
    ccncf
    co
    #
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
    wcel
    cF
    @11
    wcel
    cN
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cF
    cdm
    #
    cc
    ccncf
    co
    #
    wcel
    #
    wa
    @2
    @4
    @12
    cF
    @0
    @1
    @4
    cN
    vn
    cn0
    vn
    cv
    #
    @6
    cfv
    #
    @9
    wcel
    #
    vf
    @11
    crab
    #
    cmpt
    #
    cfv
    @12
    @0
    cN
    @3
    @22
    cS
    vf
    vn
    cpnfval
    fveq1d
    vn
    cN
    @21
    @12
    cn0
    @22
    @18
    cN
    wceq
    #
    @20
    @10
    vf
    @11
    @23
    @19
    @7
    @9
    @18
    cN
    @6
    fveq2
    eleq1d
    rabbidv
    @22
    eqid
    @10
    vf
    @11
    cc
    cS
    cpm
    ovex
    rabex
    fvmpt
    sylan9eq
    eleq2d
    @10
    @17
    vf
    cF
    @11
    @5
    cF
    wceq
    #
    @7
    @14
    @9
    @16
    @24
    cN
    @6
    @13
    @5
    cF
    cS
    cdvn
    oveq2
    fveq1d
    @24
    @8
    @15
    cc
    ccncf
    @5
    cF
    dmeq
    oveq1d
    eleq12d
    elrab
    syl6bb
end
