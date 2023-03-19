include "clmod.mm"
include "wcel.mm"
include "clfn.mm"
include "cfv.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lcdvbaselfl.mm"
include "lflcl.mm"
include "syl3anc.mm"

theorem lcdvbasecl
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcdvbasecl.h: |- H = ( LHyp ` K )
  assume lcdvbasecl.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvbasecl.v: |- V = ( Base ` U )
  assume lcdvbasecl.s: |- S = ( Scalar ` U )
  assume lcdvbasecl.r: |- R = ( Base ` S )
  assume lcdvbasecl.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvbasecl.e: |- E = ( Base ` C )
  assume lcdvbasecl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvbasecl.f: |- ( ph -> F e. E )
  assume lcdvbasecl.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( F ` X ) e. R )

  proof
    wph
    cU
    clmod
    wcel
    cF
    cU
    clfn
    cfv
    #
    wcel
    cX
    cV
    wcel
    cX
    cF
    cfv
    cR
    wcel
    wph
    cU
    cH
    cK
    cW
    lcdvbasecl.h
    lcdvbasecl.u
    lcdvbasecl.k
    dvhlmod
    wph
    cC
    cU
    @0
    cH
    cK
    cE
    cW
    cF
    lcdvbasecl.h
    lcdvbasecl.c
    lcdvbasecl.e
    lcdvbasecl.u
    @0
    eqid
    #
    lcdvbasecl.k
    lcdvbasecl.f
    lcdvbaselfl
    lcdvbasecl.x
    cS
    @0
    cF
    cR
    cV
    cU
    cX
    clmod
    lcdvbasecl.s
    lcdvbasecl.r
    lcdvbasecl.v
    @1
    lflcl
    syl3anc
end
