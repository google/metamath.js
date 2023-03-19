include "cdm.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "ctopn.mm"
include "cfv.mm"
include "wss.mm"
include "crab.mm"
include "crn.mm"
include "cfg.mm"
include "cflf.mm"
include "ctsu.mm"
include "oveq1d.mm"
include "cvv.mm"
include "wcel.mm"
include "resexg.mm"
include "syl.mm"
include "gsumpropd.mm"
include "mpteq2dv.mm"
include "fveq12d.mm"
include "cbs.mm"
include "eqid.mm"
include "eqidd.mm"
include "tsmsval2.mm"
include "3eqtr4d.mm"

theorem tsmspropd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume tsmspropd.f: |- ( ph -> F e. V )
  assume tsmspropd.g: |- ( ph -> G e. W )
  assume tsmspropd.h: |- ( ph -> H e. X )
  assume tsmspropd.b: |- ( ph -> ( Base ` G ) = ( Base ` H ) )
  assume tsmspropd.p: |- ( ph -> ( +g ` G ) = ( +g ` H ) )
  assume tsmspropd.j: |- ( ph -> ( TopOpen ` G ) = ( TopOpen ` H ) )


  assert |- ( ph -> ( G tsums F ) = ( H tsums F ) )

  proof
    wph
    vy
    cF
    cdm
    #
    cpw
    cfn
    cin
    #
    cG
    cF
    vy
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    cG
    ctopn
    cfv
    #
    @1
    vz
    @1
    vz
    cv
    @2
    wss
    vy
    @1
    crab
    cmpt
    crn
    #
    cfg
    co
    #
    cflf
    co
    #
    cfv
    vy
    @1
    cH
    @3
    cgsu
    co
    #
    cmpt
    #
    cH
    ctopn
    cfv
    #
    @8
    cflf
    co
    #
    cfv
    cG
    cF
    ctsu
    co
    cH
    cF
    ctsu
    co
    wph
    @5
    @11
    @9
    @13
    wph
    @6
    @12
    @8
    cflf
    tsmspropd.j
    oveq1d
    wph
    vy
    @1
    @4
    @10
    wph
    @3
    cG
    cH
    cvv
    cW
    cX
    wph
    cF
    cV
    wcel
    @3
    cvv
    wcel
    tsmspropd.f
    cF
    @2
    cV
    resexg
    syl
    tsmspropd.g
    tsmspropd.h
    tsmspropd.b
    tsmspropd.p
    gsumpropd
    mpteq2dv
    fveq12d
    wph
    vy
    vz
    @0
    cG
    cbs
    cfv
    #
    @1
    cF
    cG
    @6
    @7
    cW
    cV
    @14
    eqid
    @6
    eqid
    @1
    eqid
    #
    @7
    eqid
    #
    tsmspropd.g
    tsmspropd.f
    wph
    @0
    eqidd
    #
    tsmsval2
    wph
    vy
    vz
    @0
    cH
    cbs
    cfv
    #
    @1
    cF
    cH
    @12
    @7
    cX
    cV
    @18
    eqid
    @12
    eqid
    @15
    @16
    tsmspropd.h
    tsmspropd.f
    @17
    tsmsval2
    3eqtr4d
end
