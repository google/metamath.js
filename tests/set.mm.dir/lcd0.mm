include "c0g.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "oppr0.mm"
include "3eqtr4g.mm"

theorem lcd0
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  assume lcd0.h: |- H = ( LHyp ` K )
  assume lcd0.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcd0.f: |- F = ( Scalar ` U )
  assume lcd0.z: |- .0. = ( 0g ` F )
  assume lcd0.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcd0.s: |- S = ( Scalar ` C )
  assume lcd0.o: |- O = ( 0g ` S )
  assume lcd0.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> O = .0. )

  proof
    wph
    cS
    c0g
    cfv
    cF
    coppr
    cfv
    #
    c0g
    cfv
    cO
    c.0
    wph
    cS
    @0
    c0g
    wph
    cC
    cS
    cU
    cF
    cH
    cK
    @0
    cW
    lcd0.h
    lcd0.u
    lcd0.f
    @0
    eqid
    #
    lcd0.c
    lcd0.s
    lcd0.k
    lcdsca
    fveq2d
    lcd0.o
    cF
    @0
    c.0
    @1
    lcd0.z
    oppr0
    3eqtr4g
end
