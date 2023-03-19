include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "ciun.mm"
include "mapdval2N.mm"
include "iunrab.mm"
include "syl6eqr.mm"

theorem mapdval3N
  let wph: wff ph
  let vv: setvar v
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  assume mapdval2.h: |- H = ( LHyp ` K )
  assume mapdval2.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval2.s: |- S = ( LSubSp ` U )
  assume mapdval2.n: |- N = ( LSpan ` U )
  assume mapdval2.f: |- F = ( LFnl ` U )
  assume mapdval2.l: |- L = ( LKer ` U )
  assume mapdval2.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval2.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdval2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdval2.t: |- ( ph -> T e. S )
  assume mapdval2.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }

  disjoint C v
  disjoint f g
  disjoint F f
  disjoint F g
  disjoint K f
  disjoint g v
  disjoint L g
  disjoint L v
  disjoint N v
  disjoint O g
  disjoint O v
  disjoint f v
  disjoint T f
  disjoint T v
  disjoint U v
  disjoint W f
  disjoint f ph
  disjoint ph v
  disjoint C f
  assert |- ( ph -> ( M ` T ) = U_ v e. T { f e. C | ( O ` ( L ` f ) ) = ( N ` { v } ) } )

  proof
    wph
    cT
    cM
    cfv
    vf
    cv
    cL
    cfv
    cO
    cfv
    vv
    cv
    csn
    cN
    cfv
    wceq
    #
    vv
    cT
    wrex
    vf
    cC
    crab
    vv
    cT
    @0
    vf
    cC
    crab
    ciun
    wph
    vv
    cC
    cS
    cT
    cU
    vf
    vg
    cF
    cH
    cK
    cL
    cM
    cN
    cO
    cW
    mapdval2.h
    mapdval2.u
    mapdval2.s
    mapdval2.n
    mapdval2.f
    mapdval2.l
    mapdval2.o
    mapdval2.m
    mapdval2.k
    mapdval2.t
    mapdval2.c
    mapdval2N
    @0
    vv
    vf
    cT
    cC
    iunrab
    syl6eqr
end
