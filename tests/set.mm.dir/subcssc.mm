include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "ccid.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "cdm.mm"
include "wa.mm"
include "csubc.mm"
include "eqid.mm"
include "ccat.mm"
include "subcrcl.mm"
include "syl.mm"
include "eqidd.mm"
include "issubc.mm"
include "mpbid.mm"
include "simpld.mm"

theorem subcssc
  let wph: wff ph
  let cC: class C
  let cH: class H
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume subcixp.1: |- ( ph -> J e. ( Subcat ` C ) )
  assume subcssc.h: |- H = ( Homf ` C )


  assert |- ( ph -> J C_cat H )

  proof
    wph
    cJ
    cH
    cssc
    wbr
    #
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    @1
    @1
    cJ
    co
    wcel
    vg
    cv
    vf
    cv
    @1
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    @1
    @4
    cJ
    co
    wcel
    vg
    @3
    @4
    cJ
    co
    wral
    vf
    @1
    @3
    cJ
    co
    wral
    vz
    cJ
    cdm
    cdm
    #
    wral
    vy
    @6
    wral
    wa
    vx
    @6
    wral
    #
    wph
    cJ
    cC
    csubc
    cfv
    wcel
    #
    @0
    @7
    wa
    subcixp.1
    wph
    vx
    vy
    vz
    cC
    @6
    @5
    @2
    vf
    vg
    cH
    cJ
    subcssc.h
    @2
    eqid
    @5
    eqid
    wph
    @8
    cC
    ccat
    wcel
    subcixp.1
    cC
    cJ
    subcrcl
    syl
    wph
    @6
    eqidd
    issubc
    mpbid
    simpld
end
