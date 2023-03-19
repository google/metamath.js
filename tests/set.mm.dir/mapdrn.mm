include "clss.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wf1o.mm"
include "wfo.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "mapd1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"

theorem mapdrn
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  assume mapdrn.h: |- H = ( LHyp ` K )
  assume mapdrn.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdrn.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdrn.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdrn.f: |- F = ( LFnl ` U )
  assume mapdrn.l: |- L = ( LKer ` U )
  assume mapdrn.d: |- D = ( LDual ` U )
  assume mapdrn.t: |- T = ( LSubSp ` D )
  assume mapdrn.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }
  assume mapdrn.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint F g
  disjoint K g
  disjoint L g
  disjoint O g
  disjoint U g
  disjoint W g
  assert |- ( ph -> ran M = ( T i^i ~P C ) )

  proof
    wph
    cU
    clss
    cfv
    #
    cT
    cC
    cpw
    cin
    #
    cM
    wf1o
    @0
    @1
    cM
    wfo
    cM
    crn
    @1
    wceq
    wph
    cC
    cD
    @0
    cT
    cU
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    mapdrn.h
    mapdrn.o
    mapdrn.m
    mapdrn.u
    @0
    eqid
    mapdrn.f
    mapdrn.l
    mapdrn.d
    mapdrn.t
    mapdrn.c
    mapdrn.k
    mapd1o
    @0
    @1
    cM
    f1ofo
    @0
    @1
    cM
    forn
    3syl
end
