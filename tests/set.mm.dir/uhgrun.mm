include "cuhgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cun.mm"
include "uhgrf.mm"
include "syl.mm"
include "eqid.mm"
include "eqcomd.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "feq3d.mm"
include "mpbird.mm"
include "fun2d.mm"
include "dmeqd.mm"
include "dmun.mm"
include "syl6eq.mm"
include "feq123d.mm"
include "wb.mm"
include "isuhgr.mm"

theorem uhgrun
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  assume uhgrun.g: |- ( ph -> G e. UHGraph )
  assume uhgrun.h: |- ( ph -> H e. UHGraph )
  assume uhgrun.e: |- E = ( iEdg ` G )
  assume uhgrun.f: |- F = ( iEdg ` H )
  assume uhgrun.vg: |- V = ( Vtx ` G )
  assume uhgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume uhgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )
  assume uhgrun.u: |- ( ph -> U e. W )
  assume uhgrun.v: |- ( ph -> ( Vtx ` U ) = V )
  assume uhgrun.un: |- ( ph -> ( iEdg ` U ) = ( E u. F ) )


  assert |- ( ph -> U e. UHGraph )

  proof
    wph
    cU
    cuhgr
    wcel
    #
    cU
    ciedg
    cfv
    #
    cdm
    #
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
    cV
    cpw
    #
    @5
    cdif
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
    cuhgr
    wcel
    @8
    @12
    cE
    wf
    uhgrun.g
    cE
    cG
    cV
    uhgrun.vg
    uhgrun.e
    uhgrf
    syl
    wph
    @9
    @12
    cF
    wf
    @9
    cH
    cvtx
    cfv
    #
    cpw
    #
    @5
    cdif
    #
    cF
    wf
    #
    wph
    cH
    cuhgr
    wcel
    @17
    uhgrun.h
    cF
    cH
    @14
    @14
    eqid
    uhgrun.f
    uhgrf
    syl
    wph
    @12
    @16
    cF
    @9
    wph
    @11
    @15
    @5
    wph
    cV
    @14
    wph
    @14
    cV
    uhgrun.vh
    eqcomd
    pweqd
    difeq1d
    feq3d
    mpbird
    uhgrun.i
    fun2d
    wph
    @2
    @10
    @6
    @12
    @1
    @13
    uhgrun.un
    wph
    @2
    @13
    cdm
    @10
    wph
    @1
    @13
    uhgrun.un
    dmeqd
    cE
    cF
    dmun
    syl6eq
    wph
    @4
    @11
    @5
    wph
    @3
    cV
    uhgrun.v
    pweqd
    difeq1d
    feq123d
    mpbird
    wph
    cU
    cW
    wcel
    @0
    @7
    wb
    uhgrun.u
    cW
    @1
    cU
    @3
    @3
    eqid
    @1
    eqid
    isuhgr
    syl
    mpbird
end
