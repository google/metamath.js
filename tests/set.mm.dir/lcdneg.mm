include "cminusg.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "opprneg.mm"
include "3eqtr4g.mm"

theorem lcdneg
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  assume lcdneg.h: |- H = ( LHyp ` K )
  assume lcdneg.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdneg.r: |- R = ( Scalar ` U )
  assume lcdneg.m: |- M = ( invg ` R )
  assume lcdneg.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdneg.s: |- S = ( Scalar ` C )
  assume lcdneg.n: |- N = ( invg ` S )
  assume lcdneg.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> N = M )

  proof
    wph
    cS
    cminusg
    cfv
    cR
    coppr
    cfv
    #
    cminusg
    cfv
    cN
    cM
    wph
    cS
    @0
    cminusg
    wph
    cC
    cS
    cU
    cR
    cH
    cK
    @0
    cW
    lcdneg.h
    lcdneg.u
    lcdneg.r
    @0
    eqid
    #
    lcdneg.c
    lcdneg.s
    lcdneg.k
    lcdsca
    fveq2d
    lcdneg.n
    cR
    cM
    @0
    @1
    lcdneg.m
    opprneg
    3eqtr4g
end
