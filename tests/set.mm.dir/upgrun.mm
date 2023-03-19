include "cupgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "cun.mm"
include "upgrf.mm"
include "syl.mm"
include "eqid.mm"
include "eqcomd.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "rabeqdv.mm"
include "feq3d.mm"
include "mpbird.mm"
include "fun2d.mm"
include "dmeqd.mm"
include "dmun.mm"
include "syl6eq.mm"
include "feq123d.mm"
include "wb.mm"
include "isupgr.mm"

theorem upgrun
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume upgrun.g: |- ( ph -> G e. UPGraph )
  assume upgrun.h: |- ( ph -> H e. UPGraph )
  assume upgrun.e: |- E = ( iEdg ` G )
  assume upgrun.f: |- F = ( iEdg ` H )
  assume upgrun.vg: |- V = ( Vtx ` G )
  assume upgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume upgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )
  assume upgrun.u: |- ( ph -> U e. W )
  assume upgrun.v: |- ( ph -> ( Vtx ` U ) = V )
  assume upgrun.un: |- ( ph -> ( iEdg ` U ) = ( E u. F ) )


  assert |- ( ph -> U e. UPGraph )

  proof
    wph
    cU
    cupgr
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
    cle
    wbr
    #
    vx
    cU
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    @1
    wf
    #
    wph
    @9
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
    @6
    cdif
    #
    crab
    #
    cE
    cF
    cun
    #
    wf
    wph
    @10
    @11
    @15
    cE
    cF
    wph
    cG
    cupgr
    wcel
    @10
    @15
    cE
    wf
    upgrun.g
    vx
    cE
    cG
    cV
    upgrun.vg
    upgrun.e
    upgrf
    syl
    wph
    @11
    @15
    cF
    wf
    @11
    @3
    vx
    cH
    cvtx
    cfv
    #
    cpw
    #
    @6
    cdif
    #
    crab
    #
    cF
    wf
    #
    wph
    cH
    cupgr
    wcel
    @21
    upgrun.h
    vx
    cF
    cH
    @17
    @17
    eqid
    upgrun.f
    upgrf
    syl
    wph
    @15
    @20
    cF
    @11
    wph
    @3
    vx
    @14
    @19
    wph
    @13
    @18
    @6
    wph
    cV
    @17
    wph
    @17
    cV
    upgrun.vh
    eqcomd
    pweqd
    difeq1d
    rabeqdv
    feq3d
    mpbird
    upgrun.i
    fun2d
    wph
    @2
    @12
    @8
    @15
    @1
    @16
    upgrun.un
    wph
    @2
    @16
    cdm
    @12
    wph
    @1
    @16
    upgrun.un
    dmeqd
    cE
    cF
    dmun
    syl6eq
    wph
    @3
    vx
    @7
    @14
    wph
    @5
    @13
    @6
    wph
    @4
    cV
    upgrun.v
    pweqd
    difeq1d
    rabeqdv
    feq123d
    mpbird
    wph
    cU
    cW
    wcel
    @0
    @9
    wb
    upgrun.u
    vx
    cW
    @1
    cU
    @4
    @4
    eqid
    @1
    eqid
    isupgr
    syl
    mpbird
end
