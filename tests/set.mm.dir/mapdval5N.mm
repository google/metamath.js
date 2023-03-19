include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "ciun.mm"
include "mapdval4N.mm"
include "iunrab.mm"
include "syl6eqr.mm"

theorem mapdval5N
  let wph: wff ph
  let vv: setvar v
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  let vg: setvar g
  let vw: setvar w
  assume mapdval4.h: |- H = ( LHyp ` K )
  assume mapdval4.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval4.s: |- S = ( LSubSp ` U )
  assume mapdval4.f: |- F = ( LFnl ` U )
  assume mapdval4.l: |- L = ( LKer ` U )
  assume mapdval4.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval4.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdval4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdval4.t: |- ( ph -> T e. S )

  disjoint f v
  disjoint F f
  disjoint F v
  disjoint K f
  disjoint L v
  disjoint O v
  disjoint T f
  disjoint T v
  disjoint U v
  disjoint W f
  disjoint f ph
  disjoint ph v
  disjoint f g
  disjoint f w
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint v w
  disjoint F w
  disjoint L g
  disjoint L w
  disjoint O g
  disjoint O w
  disjoint T w
  disjoint U w
  disjoint ph w
  assert |- ( ph -> ( M ` T ) = U_ v e. T { f e. F | ( O ` { v } ) = ( L ` f ) } )

  proof
    wph
    cT
    cM
    cfv
    vv
    cv
    csn
    cO
    cfv
    vf
    cv
    cL
    cfv
    wceq
    #
    vv
    cT
    wrex
    vf
    cF
    crab
    vv
    cT
    @0
    vf
    cF
    crab
    ciun
    wph
    vv
    cS
    cT
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    mapdval4.h
    mapdval4.u
    mapdval4.s
    mapdval4.f
    mapdval4.l
    mapdval4.o
    mapdval4.m
    mapdval4.k
    mapdval4.t
    mapdval4N
    @0
    vv
    vf
    cT
    cF
    iunrab
    syl6eqr
end
