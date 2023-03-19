include "cc.mm"
include "wss.mm"
include "wf.mm"
include "wa.mm"
include "cdv.mm"
include "co.mm"
include "cres.mm"
include "wrel.mm"
include "relres.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "cop.mm"
include "w3a.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "eqid.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "dvcl.mm"
include "mpdan.mm"
include "simp3r.mm"
include "dvres2lem.mm"
include "3expia.mm"
include "vex.mm"
include "brres.mm"
include "df-br.mm"
include "bitr3i.mm"
include "3imtr3g.mm"
include "relssdv.mm"

theorem dvres2
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( S C_ CC /\ F : A --> CC ) /\ ( A C_ S /\ B C_ S ) ) -> ( ( S _D F ) |` B ) C_ ( B _D ( F |` B ) ) )

  proof
    cS
    cc
    wss
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    cA
    cS
    wss
    #
    cB
    cS
    wss
    #
    wa
    #
    wa
    #
    vx
    vy
    cS
    cF
    cdv
    co
    #
    cB
    cres
    #
    cB
    cF
    cB
    cres
    cdv
    co
    #
    @8
    wrel
    @6
    @7
    cB
    relres
    a1i
    @6
    vx
    cv
    #
    vy
    cv
    #
    @7
    wbr
    #
    @10
    cB
    wcel
    #
    wa
    #
    @10
    @11
    @9
    wbr
    #
    @10
    @11
    cop
    #
    @8
    wcel
    #
    @16
    @9
    wcel
    @2
    @5
    @14
    @15
    @2
    @5
    @14
    w3a
    #
    vx
    vy
    vz
    cA
    cB
    cS
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    cF
    vz
    cA
    @10
    csn
    cdif
    vz
    cv
    #
    cF
    cfv
    @10
    cF
    cfv
    cmin
    co
    @21
    @10
    cmin
    co
    cdiv
    co
    cmpt
    #
    @19
    @19
    eqid
    @20
    eqid
    @22
    eqid
    @0
    @1
    @5
    @14
    simp1l
    #
    @0
    @1
    @5
    @14
    simp1r
    #
    @2
    @3
    @4
    @14
    simp2l
    #
    @2
    @3
    @4
    @14
    simp2r
    @18
    @12
    @11
    cc
    wcel
    @2
    @5
    @12
    @13
    simp3l
    #
    @18
    cA
    @10
    @11
    cS
    cF
    @23
    @24
    @25
    dvcl
    mpdan
    @26
    @2
    @5
    @12
    @13
    simp3r
    dvres2lem
    3expia
    @14
    @10
    @11
    @8
    wbr
    @17
    @10
    @11
    @7
    cB
    vy
    vex
    brres
    @10
    @11
    @8
    df-br
    bitr3i
    @10
    @11
    @9
    df-br
    3imtr3g
    relssdv
end
