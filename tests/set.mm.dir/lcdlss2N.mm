include "cv.mm"
include "clk.mm"
include "cfv.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cpw.mm"
include "cin.mm"
include "eqid.mm"
include "lcdlss.mm"
include "lcdvbase.mm"
include "pweqd.mm"
include "ineq2d.mm"
include "eqtr4d.mm"

theorem lcdlss2N
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  assume lcdlss2.h: |- H = ( LHyp ` K )
  assume lcdlss2.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlss2.s: |- S = ( LSubSp ` C )
  assume lcdlss2.v: |- V = ( Base ` C )
  assume lcdlss2.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdlss2.d: |- D = ( LDual ` U )
  assume lcdlss2.t: |- T = ( LSubSp ` D )
  assume lcdlss2.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> S = ( T i^i ~P V ) )

  proof
    wph
    cS
    cT
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
    cpw
    #
    cin
    cT
    cV
    cpw
    #
    cin
    wph
    @4
    cC
    cD
    cS
    cT
    cU
    vf
    @3
    cH
    cK
    @0
    @2
    cW
    lcdlss2.h
    @2
    eqid
    #
    lcdlss2.c
    lcdlss2.s
    lcdlss2.u
    @3
    eqid
    #
    @0
    eqid
    #
    lcdlss2.d
    lcdlss2.t
    @4
    eqid
    #
    lcdlss2.k
    lcdlss
    wph
    @6
    @5
    cT
    wph
    cV
    @4
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
    cV
    cW
    lcdlss2.h
    @7
    lcdlss2.c
    lcdlss2.v
    lcdlss2.u
    @8
    @9
    @10
    lcdlss2.k
    lcdvbase
    pweqd
    ineq2d
    eqtr4d
end
