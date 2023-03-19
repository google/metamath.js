include "cplusg.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "oppradd.mm"
include "3eqtr4g.mm"

theorem lcdsadd
  let wph: wff ph
  let cC: class C
  let c.pl: class .+
  let c.pb: class .+b
  let cS: class S
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume lcdsadd.h: |- H = ( LHyp ` K )
  assume lcdsadd.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdsadd.f: |- F = ( Scalar ` U )
  assume lcdsadd.p: |- .+ = ( +g ` F )
  assume lcdsadd.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdsadd.s: |- S = ( Scalar ` C )
  assume lcdsadd.a: |- .+b = ( +g ` S )
  assume lcdsadd.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> .+b = .+ )

  proof
    wph
    cS
    cplusg
    cfv
    cF
    coppr
    cfv
    #
    cplusg
    cfv
    c.pb
    c.pl
    wph
    cS
    @0
    cplusg
    wph
    cC
    cS
    cU
    cF
    cH
    cK
    @0
    cW
    lcdsadd.h
    lcdsadd.u
    lcdsadd.f
    @0
    eqid
    #
    lcdsadd.c
    lcdsadd.s
    lcdsadd.k
    lcdsca
    fveq2d
    lcdsadd.a
    c.pl
    cF
    @0
    @1
    lcdsadd.p
    oppradd
    3eqtr4g
end
