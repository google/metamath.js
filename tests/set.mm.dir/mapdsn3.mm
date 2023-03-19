include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "mapdsn2.mm"
include "dvhlvec.mm"
include "ldual1dim.mm"
include "eqtr4d.mm"

theorem mapdsn3
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  assume mapdsn3.h: |- H = ( LHyp ` K )
  assume mapdsn3.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdsn3.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdsn3.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdsn3.v: |- V = ( Base ` U )
  assume mapdsn3.n: |- N = ( LSpan ` U )
  assume mapdsn3.f: |- F = ( LFnl ` U )
  assume mapdsn3.l: |- L = ( LKer ` U )
  assume mapdsn3.d: |- D = ( LDual ` U )
  assume mapdsn3.p: |- P = ( LSpan ` D )
  assume mapdsn3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdsn3.x: |- ( ph -> X e. V )
  assume mapdsn3.g: |- ( ph -> G e. F )
  assume mapdsn3.e: |- ( ph -> ( L ` G ) = ( O ` { X } ) )


  assert |- ( ph -> ( M ` ( N ` { X } ) ) = ( P ` { G } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    cM
    cfv
    cG
    cL
    cfv
    vf
    cv
    cL
    cfv
    wss
    vf
    cF
    crab
    cG
    csn
    cP
    cfv
    wph
    cU
    vf
    cF
    cG
    cH
    cK
    cL
    cM
    cN
    cO
    cV
    cW
    cX
    mapdsn3.h
    mapdsn3.o
    mapdsn3.m
    mapdsn3.u
    mapdsn3.v
    mapdsn3.n
    mapdsn3.f
    mapdsn3.l
    mapdsn3.k
    mapdsn3.x
    mapdsn3.e
    mapdsn2
    wph
    cD
    vf
    cF
    cG
    cL
    cP
    cU
    mapdsn3.f
    mapdsn3.l
    mapdsn3.d
    mapdsn3.p
    wph
    cU
    cH
    cK
    cW
    mapdsn3.h
    mapdsn3.u
    mapdsn3.k
    dvhlvec
    mapdsn3.g
    ldual1dim
    eqtr4d
end
