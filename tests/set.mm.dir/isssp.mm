include "cnv.mm"
include "wcel.mm"
include "cv.mm"
include "cpv.mm"
include "cfv.mm"
include "wss.mm"
include "cns.mm"
include "cnmcv.mm"
include "w3a.mm"
include "crab.mm"
include "wa.mm"
include "sspval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sseq1d.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isssp
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cW: class W
  let vw: setvar w
  assume isssp.g: |- G = ( +v ` U )
  assume isssp.f: |- F = ( +v ` W )
  assume isssp.s: |- S = ( .sOLD ` U )
  assume isssp.r: |- R = ( .sOLD ` W )
  assume isssp.n: |- N = ( normCV ` U )
  assume isssp.m: |- M = ( normCV ` W )
  assume isssp.h: |- H = ( SubSp ` U )


  assert |- ( U e. NrmCVec -> ( W e. H <-> ( W e. NrmCVec /\ ( F C_ G /\ R C_ S /\ M C_ N ) ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    cW
    vw
    cv
    #
    cpv
    cfv
    #
    cG
    wss
    #
    @1
    cns
    cfv
    #
    cS
    wss
    #
    @1
    cnmcv
    cfv
    #
    cN
    wss
    #
    w3a
    #
    vw
    cnv
    crab
    #
    wcel
    cW
    cnv
    wcel
    cF
    cG
    wss
    #
    cR
    cS
    wss
    #
    cM
    cN
    wss
    #
    w3a
    #
    wa
    @0
    cH
    @9
    cW
    vw
    cS
    cU
    cG
    cH
    cN
    isssp.g
    isssp.s
    isssp.n
    isssp.h
    sspval
    eleq2d
    @8
    @13
    vw
    cW
    cnv
    @1
    cW
    wceq
    #
    @3
    @10
    @5
    @11
    @7
    @12
    @14
    @2
    cF
    cG
    @14
    @2
    cW
    cpv
    cfv
    cF
    @1
    cW
    cpv
    fveq2
    isssp.f
    syl6eqr
    sseq1d
    @14
    @4
    cR
    cS
    @14
    @4
    cW
    cns
    cfv
    cR
    @1
    cW
    cns
    fveq2
    isssp.r
    syl6eqr
    sseq1d
    @14
    @6
    cM
    cN
    @14
    @6
    cW
    cnmcv
    cfv
    cM
    @1
    cW
    cnmcv
    fveq2
    isssp.m
    syl6eqr
    sseq1d
    3anbi123d
    elrab
    syl6bb
end
