include "clss.mm"
include "cfv.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsatlssel.mm"
include "mapdval4N.mm"

theorem mapd1dim2lem1N
  let wph: wff ph
  let vv: setvar v
  let cA: class A
  let cQ: class Q
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  assume mapd1dim2.h: |- H = ( LHyp ` K )
  assume mapd1dim2.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapd1dim2.a: |- A = ( LSAtoms ` U )
  assume mapd1dim2.f: |- F = ( LFnl ` U )
  assume mapd1dim2.l: |- L = ( LKer ` U )
  assume mapd1dim2.o: |- O = ( ( ocH ` K ) ` W )
  assume mapd1dim2.m: |- M = ( ( mapd ` K ) ` W )
  assume mapd1dim2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapd1dim2.t: |- ( ph -> Q e. A )

  disjoint f v
  disjoint F f
  disjoint F v
  disjoint K f
  disjoint L v
  disjoint O v
  disjoint Q f
  disjoint Q v
  disjoint U v
  disjoint W f
  disjoint f ph
  disjoint ph v
  assert |- ( ph -> ( M ` Q ) = { f e. F | E. v e. Q ( O ` { v } ) = ( L ` f ) } )

  proof
    wph
    vv
    cU
    clss
    cfv
    #
    cQ
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    mapd1dim2.h
    mapd1dim2.u
    @0
    eqid
    #
    mapd1dim2.f
    mapd1dim2.l
    mapd1dim2.o
    mapd1dim2.m
    mapd1dim2.k
    wph
    cA
    @0
    cQ
    cU
    @1
    mapd1dim2.a
    wph
    cU
    cH
    cK
    cW
    mapd1dim2.h
    mapd1dim2.u
    mapd1dim2.k
    dvhlmod
    mapd1dim2.t
    lsatlssel
    mapdval4N
end
