include "cv.mm"
include "clk.mm"
include "cfv.mm"
include "coch.mm"
include "wceq.mm"
include "crab.mm"
include "eqid.mm"
include "lcdvbase.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem lcdvbasess
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  assume lcdvbasess.h: |- H = ( LHyp ` K )
  assume lcdvbasess.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvbasess.v: |- V = ( Base ` C )
  assume lcdvbasess.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvbasess.f: |- F = ( LFnl ` U )
  assume lcdvbasess.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> V C_ F )

  proof
    wph
    cV
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
    #
    vf
    cF
    crab
    #
    cF
    wph
    @4
    cC
    cU
    vf
    cF
    cH
    cK
    @0
    @2
    cV
    cW
    lcdvbasess.h
    @2
    eqid
    lcdvbasess.c
    lcdvbasess.v
    lcdvbasess.u
    lcdvbasess.f
    @0
    eqid
    @4
    eqid
    lcdvbasess.k
    lcdvbase
    @3
    vf
    cF
    ssrab2
    syl6eqss
end
