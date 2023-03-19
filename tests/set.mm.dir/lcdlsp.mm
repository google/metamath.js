include "cfv.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "clspn.mm"
include "chlt.mm"
include "eqid.mm"
include "lcdval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lduallmod.mm"
include "lclkr.mm"
include "lcdvbase.mm"
include "sseqtrd.mm"
include "lsslsp.mm"
include "syl3anc.mm"
include "eqtr4d.mm"

theorem lcdlsp
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let vf: setvar f
  assume lcdlsp.h: |- H = ( LHyp ` K )
  assume lcdlsp.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdlsp.d: |- D = ( LDual ` U )
  assume lcdlsp.m: |- M = ( LSpan ` D )
  assume lcdlsp.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlsp.f: |- F = ( Base ` C )
  assume lcdlsp.n: |- N = ( LSpan ` C )
  assume lcdlsp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdlsp.g: |- ( ph -> G C_ F )


  assert |- ( ph -> ( N ` G ) = ( M ` G ) )

  proof
    wph
    cG
    cN
    cfv
    cG
    cD
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
    @2
    cfv
    @1
    wceq
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    clspn
    cfv
    #
    cfv
    #
    cG
    cM
    cfv
    #
    wph
    cG
    cN
    @6
    wph
    cN
    cC
    clspn
    cfv
    @6
    lcdlsp.n
    wph
    cC
    @5
    clspn
    wph
    cC
    cD
    cU
    vf
    @3
    cH
    cK
    @0
    @2
    cW
    chlt
    lcdlsp.h
    @2
    eqid
    #
    lcdlsp.c
    lcdlsp.u
    @3
    eqid
    #
    @0
    eqid
    #
    lcdlsp.d
    lcdlsp.k
    lcdval
    fveq2d
    syl5eq
    fveq1d
    wph
    cD
    clmod
    wcel
    @4
    cD
    clss
    cfv
    #
    wcel
    cG
    @4
    wss
    @8
    @7
    wceq
    wph
    cD
    cU
    lcdlsp.d
    wph
    cU
    cH
    cK
    cW
    lcdlsp.h
    lcdlsp.u
    lcdlsp.k
    dvhlmod
    lduallmod
    wph
    @4
    cD
    @12
    cU
    vf
    @3
    cH
    cK
    @0
    @2
    cW
    lcdlsp.h
    lcdlsp.u
    @9
    @10
    @11
    lcdlsp.d
    @12
    eqid
    #
    @4
    eqid
    #
    lcdlsp.k
    lclkr
    wph
    cG
    cF
    @4
    lcdlsp.g
    wph
    @4
    cC
    cU
    vf
    @3
    cH
    cK
    @0
    @2
    cF
    cW
    lcdlsp.h
    @9
    lcdlsp.c
    lcdlsp.f
    lcdlsp.u
    @10
    @11
    @14
    lcdlsp.k
    lcdvbase
    sseqtrd
    @4
    cG
    @12
    cM
    @6
    cD
    @5
    @5
    eqid
    lcdlsp.m
    @6
    eqid
    @13
    lsslsp
    syl3anc
    eqtr4d
end
