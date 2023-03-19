include "climc.mm"
include "co.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccnp.mm"
include "cab.mm"
include "wss.mm"
include "wf.mm"
include "w3a.mm"
include "wa.mm"
include "limcrcl.mm"
include "eqid.mm"
include "limcfval.mm"
include "syl.mm"
include "simprd.mm"
include "id.mm"
include "sseldd.mm"
include "ssriv.mm"

theorem limccl
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cA: class A
  let wph: wff ph
  let cC: class C
  let cK: class K


  assert |- ( F limCC B ) C_ CC

  proof
    vx
    cF
    cB
    climc
    co
    #
    cc
    vx
    cv
    #
    @0
    wcel
    #
    @0
    cc
    @1
    @2
    @0
    vz
    cF
    cdm
    #
    cB
    csn
    cun
    #
    vz
    cv
    #
    cB
    wceq
    vy
    cv
    @5
    cF
    cfv
    cif
    cmpt
    cB
    ccnfld
    ctopn
    cfv
    #
    @4
    crest
    co
    #
    @6
    ccnp
    co
    cfv
    wcel
    vy
    cab
    wceq
    #
    @0
    cc
    wss
    #
    @2
    @3
    cc
    cF
    wf
    @3
    cc
    wss
    cB
    cc
    wcel
    w3a
    @8
    @9
    wa
    cB
    @1
    cF
    limcrcl
    vy
    vz
    @3
    cB
    cF
    @7
    @6
    @7
    eqid
    @6
    eqid
    limcfval
    syl
    simprd
    @2
    id
    sseldd
    ssriv
end
