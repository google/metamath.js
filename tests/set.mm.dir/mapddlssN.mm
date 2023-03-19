include "cfv.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "clfn.mm"
include "crab.mm"
include "chlt.mm"
include "eqid.mm"
include "mapdval.mm"
include "lclkrs.mm"
include "eqeltrd.mm"

theorem mapddlssN
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let vf: setvar f
  assume mapddlss.h: |- H = ( LHyp ` K )
  assume mapddlss.m: |- M = ( ( mapd ` K ) ` W )
  assume mapddlss.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapddlss.s: |- S = ( LSubSp ` U )
  assume mapddlss.d: |- D = ( LDual ` U )
  assume mapddlss.t: |- T = ( LSubSp ` D )
  assume mapddlss.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapddlss.r: |- ( ph -> R e. S )


  assert |- ( ph -> ( M ` R ) e. T )

  proof
    wph
    cR
    cM
    cfv
    vf
    cv
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @2
    cfv
    @1
    wceq
    @3
    cR
    wss
    wa
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cT
    wph
    cS
    cR
    cU
    vf
    @4
    cH
    cK
    @0
    cM
    @2
    cW
    chlt
    mapddlss.h
    mapddlss.u
    mapddlss.s
    @4
    eqid
    #
    @0
    eqid
    #
    @2
    eqid
    #
    mapddlss.m
    mapddlss.k
    mapddlss.r
    mapdval
    wph
    @5
    cD
    cR
    cS
    cT
    cU
    vf
    @4
    cH
    cK
    @0
    @2
    cW
    mapddlss.h
    @8
    mapddlss.u
    mapddlss.s
    @6
    @7
    mapddlss.d
    mapddlss.t
    @5
    eqid
    mapddlss.k
    mapddlss.r
    lclkrs
    eqeltrd
end
