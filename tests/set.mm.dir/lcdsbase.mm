include "cbs.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "opprbas.mm"
include "3eqtr4g.mm"

theorem lcdsbase
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  assume lcdsbase.h: |- H = ( LHyp ` K )
  assume lcdsbase.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdsbase.f: |- F = ( Scalar ` U )
  assume lcdsbase.l: |- L = ( Base ` F )
  assume lcdsbase.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdsbase.s: |- S = ( Scalar ` C )
  assume lcdsbase.r: |- R = ( Base ` S )
  assume lcdsbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> R = L )

  proof
    wph
    cS
    cbs
    cfv
    cF
    coppr
    cfv
    #
    cbs
    cfv
    cR
    cL
    wph
    cS
    @0
    cbs
    wph
    cC
    cS
    cU
    cF
    cH
    cK
    @0
    cW
    lcdsbase.h
    lcdsbase.u
    lcdsbase.f
    @0
    eqid
    #
    lcdsbase.c
    lcdsbase.s
    lcdsbase.k
    lcdsca
    fveq2d
    lcdsbase.r
    cL
    cF
    @0
    @1
    lcdsbase.l
    opprbas
    3eqtr4g
end
