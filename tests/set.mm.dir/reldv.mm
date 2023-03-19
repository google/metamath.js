include "cdv.mm"
include "co.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cdm.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "cnt.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "ciun.mm"
include "cc.mm"
include "cpm.mm"
include "wral.mm"
include "cpw.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "df-rel.mm"
include "mpbi.mm"
include "df-dv.mm"
include "ovmptss.mm"
include "ax-mp.mm"

theorem reldv
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vj: setvar j
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel ( S _D F )

  proof
    cS
    cF
    cdv
    co
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    #
    vx
    vf
    cv
    #
    cdm
    #
    ccnfld
    ctopn
    cfv
    vs
    cv
    #
    crest
    co
    cnt
    cfv
    cfv
    #
    vx
    cv
    #
    csn
    #
    vz
    @4
    @8
    cdif
    vz
    cv
    #
    @3
    cfv
    @7
    @3
    cfv
    cmin
    co
    @9
    @7
    cmin
    co
    cdiv
    co
    cmpt
    @7
    climc
    co
    #
    cxp
    #
    ciun
    #
    @1
    wss
    #
    vf
    cc
    @5
    cpm
    co
    #
    wral
    #
    vs
    cc
    cpw
    #
    wral
    @2
    @15
    vs
    @16
    @13
    vf
    @14
    @12
    wrel
    #
    @13
    @17
    @11
    wrel
    #
    vx
    @6
    wral
    @18
    vx
    @6
    @8
    @10
    relxp
    rgenw
    vx
    @6
    @11
    reliun
    mpbir
    @12
    df-rel
    mpbi
    rgenw
    rgenw
    vs
    vf
    @16
    @14
    @12
    cS
    cdv
    cF
    @1
    vx
    vz
    vf
    vs
    df-dv
    ovmptss
    ax-mp
    @0
    df-rel
    mpbir
end
