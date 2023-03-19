include "lcdvbasess.mm"
include "sseldd.mm"

theorem lcdvbaselfl
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  assume lcdvbasess.h: |- H = ( LHyp ` K )
  assume lcdvbasess.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvbasess.v: |- V = ( Base ` C )
  assume lcdvbasess.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvbasess.f: |- F = ( LFnl ` U )
  assume lcdvbasess.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvbaselfl.x: |- ( ph -> X e. V )


  assert |- ( ph -> X e. F )

  proof
    wph
    cV
    cF
    cX
    wph
    cC
    cU
    cF
    cH
    cK
    cV
    cW
    lcdvbasess.h
    lcdvbasess.c
    lcdvbasess.v
    lcdvbasess.u
    lcdvbasess.f
    lcdvbasess.k
    lcdvbasess
    lcdvbaselfl.x
    sseldd
end
