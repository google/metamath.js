include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cpm.mm"
include "wa.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "weq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "crest.mm"
include "ccnp.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wsbc.mm"
include "cab.mm"
include "df-limc.mm"
include "elmpt2cl.mm"
include "cnex.mm"
include "elpm2.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem limcrcl
  let cB: class B
  let cC: class C
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
  let cK: class K


  assert |- ( C e. ( F limCC B ) -> ( F : dom F --> CC /\ dom F C_ CC /\ B e. CC ) )

  proof
    cC
    cF
    cB
    climc
    co
    wcel
    cF
    cc
    cc
    cpm
    co
    #
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @4
    cc
    wss
    #
    @2
    w3a
    #
    vf
    vx
    @0
    cc
    vz
    vf
    cv
    #
    cdm
    vx
    cv
    #
    csn
    cun
    #
    vz
    vx
    weq
    vy
    cv
    vz
    cv
    @8
    cfv
    cif
    cmpt
    @9
    vj
    cv
    #
    @10
    crest
    co
    @11
    ccnp
    co
    cfv
    wcel
    vj
    ccnfld
    ctopn
    cfv
    wsbc
    vy
    cab
    cF
    cB
    climc
    cC
    vx
    vy
    vz
    vf
    vj
    df-limc
    elmpt2cl
    @3
    @5
    @6
    wa
    #
    @2
    wa
    @7
    @1
    @12
    @2
    cc
    cc
    cF
    cnex
    cnex
    elpm2
    anbi1i
    @5
    @6
    @2
    df-3an
    bitr4i
    sylib
end
