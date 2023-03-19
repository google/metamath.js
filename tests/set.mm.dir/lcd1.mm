include "cur.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "oppr1.mm"
include "3eqtr4g.mm"

theorem lcd1
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume lcd1.h: |- H = ( LHyp ` K )
  assume lcd1.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcd1.f: |- F = ( Scalar ` U )
  assume lcd1.j: |- .1. = ( 1r ` F )
  assume lcd1.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcd1.s: |- S = ( Scalar ` C )
  assume lcd1.i: |- I = ( 1r ` S )
  assume lcd1.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> I = .1. )

  proof
    wph
    cS
    cur
    cfv
    cF
    coppr
    cfv
    #
    cur
    cfv
    cI
    c.1
    wph
    cS
    @0
    cur
    wph
    cC
    cS
    cU
    cF
    cH
    cK
    @0
    cW
    lcd1.h
    lcd1.u
    lcd1.f
    @0
    eqid
    #
    lcd1.c
    lcd1.s
    lcd1.k
    lcdsca
    fveq2d
    lcd1.i
    cF
    c.1
    @0
    @1
    lcd1.j
    oppr1
    3eqtr4g
end
