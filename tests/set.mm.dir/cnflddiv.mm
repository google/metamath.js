include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt2.mm"
include "ccnfld.mm"
include "cinvr.mm"
include "cfv.mm"
include "cdiv.mm"
include "cdvr.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "eqid.mm"
include "cnfldmul.mm"
include "dvrcan1.mm"
include "mp3an1.mm"
include "oveq1d.mm"
include "dvrcl.mm"
include "wne.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "divcan4d.mm"
include "eqtr3d.mm"
include "simpl.mm"
include "divval.mm"
include "syl3anc.mm"
include "dvrval.mm"
include "mpt2eq3ia.mm"
include "df-div.mm"
include "dvrfval.mm"
include "3eqtr4i.mm"

theorem cnflddiv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- / = ( /r ` CCfld )

  proof
    vx
    vy
    cc
    cc
    cc0
    csn
    cdif
    #
    vy
    cv
    #
    vz
    cv
    cmul
    co
    vx
    cv
    #
    wceq
    vz
    cc
    crio
    #
    cmpt2
    vx
    vy
    cc
    @0
    @2
    @1
    ccnfld
    cinvr
    cfv
    #
    cfv
    cmul
    co
    #
    cmpt2
    cdiv
    ccnfld
    cdvr
    cfv
    #
    vx
    vy
    cc
    @0
    @3
    @5
    @2
    cc
    wcel
    #
    @1
    @0
    wcel
    #
    wa
    #
    @2
    @1
    @6
    co
    #
    @3
    @5
    @9
    @2
    @1
    cdiv
    co
    #
    @10
    @3
    @9
    @10
    @1
    cmul
    co
    #
    @1
    cdiv
    co
    @11
    @10
    @9
    @12
    @2
    @1
    cdiv
    ccnfld
    crg
    wcel
    #
    @7
    @8
    @12
    @2
    wceq
    cnring
    cc
    @6
    ccnfld
    cmul
    @0
    @2
    @1
    cnfldbas
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    #
    @6
    eqid
    #
    cnfldmul
    dvrcan1
    mp3an1
    oveq1d
    @9
    @10
    @1
    @13
    @7
    @8
    @10
    cc
    wcel
    cnring
    cc
    @6
    ccnfld
    @0
    @2
    @1
    cnfldbas
    @14
    @15
    dvrcl
    mp3an1
    @9
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    #
    @9
    @8
    @16
    @17
    wa
    @7
    @8
    simpr
    @1
    cc
    cc0
    eldifsn
    sylib
    #
    simpld
    #
    @9
    @16
    @17
    @18
    simprd
    #
    divcan4d
    eqtr3d
    @9
    @7
    @16
    @17
    @11
    @3
    wceq
    @7
    @8
    simpl
    @19
    @20
    vz
    @2
    @1
    divval
    syl3anc
    eqtr3d
    cc
    @6
    ccnfld
    cmul
    @0
    @4
    @2
    @1
    cnfldbas
    cnfldmul
    @14
    @4
    eqid
    #
    @15
    dvrval
    eqtr3d
    mpt2eq3ia
    vx
    vy
    vz
    df-div
    vx
    vy
    cc
    @6
    ccnfld
    cmul
    @0
    @4
    cnfldbas
    cnfldmul
    @14
    @21
    @15
    dvrfval
    3eqtr4i
end
