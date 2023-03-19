include "cumgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "cun.mm"
include "umgrf.mm"
include "syl.mm"
include "eqid.mm"
include "eqcomd.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "feq3d.mm"
include "mpbird.mm"
include "fun2d.mm"
include "dmeqd.mm"
include "dmun.mm"
include "syl6eq.mm"
include "feq123d.mm"
include "wb.mm"
include "isumgrs.mm"

theorem umgrun
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume umgrun.g: |- ( ph -> G e. UMGraph )
  assume umgrun.h: |- ( ph -> H e. UMGraph )
  assume umgrun.e: |- E = ( iEdg ` G )
  assume umgrun.f: |- F = ( iEdg ` H )
  assume umgrun.vg: |- V = ( Vtx ` G )
  assume umgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume umgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )
  assume umgrun.u: |- ( ph -> U e. W )
  assume umgrun.v: |- ( ph -> ( Vtx ` U ) = V )
  assume umgrun.un: |- ( ph -> ( iEdg ` U ) = ( E u. F ) )


  assert |- ( ph -> U e. UMGraph )

  proof
    wph
    cU
    cumgr
    wcel
    #
    cU
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cU
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @1
    wf
    #
    wph
    @7
    cE
    cdm
    #
    cF
    cdm
    #
    cun
    #
    @3
    vx
    cV
    cpw
    #
    crab
    #
    cE
    cF
    cun
    #
    wf
    wph
    @8
    @9
    @12
    cE
    cF
    wph
    cG
    cumgr
    wcel
    @8
    @12
    cE
    wf
    umgrun.g
    vx
    cE
    cG
    cV
    umgrun.vg
    umgrun.e
    umgrf
    syl
    wph
    @9
    @12
    cF
    wf
    @9
    @3
    vx
    cH
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    cF
    wf
    #
    wph
    cH
    cumgr
    wcel
    @17
    umgrun.h
    vx
    cF
    cH
    @14
    @14
    eqid
    umgrun.f
    umgrf
    syl
    wph
    @12
    @16
    cF
    @9
    wph
    @3
    vx
    @11
    @15
    wph
    cV
    @14
    wph
    @14
    cV
    umgrun.vh
    eqcomd
    pweqd
    rabeqdv
    feq3d
    mpbird
    umgrun.i
    fun2d
    wph
    @2
    @10
    @6
    @12
    @1
    @13
    umgrun.un
    wph
    @2
    @13
    cdm
    @10
    wph
    @1
    @13
    umgrun.un
    dmeqd
    cE
    cF
    dmun
    syl6eq
    wph
    @3
    vx
    @5
    @11
    wph
    @4
    cV
    umgrun.v
    pweqd
    rabeqdv
    feq123d
    mpbird
    wph
    cU
    cW
    wcel
    @0
    @7
    wb
    umgrun.u
    vx
    cW
    @1
    cU
    @4
    @4
    eqid
    @1
    eqid
    isumgrs
    syl
    mpbird
end
