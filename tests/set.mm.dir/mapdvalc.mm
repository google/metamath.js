include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "crab.mm"
include "mapdval.mm"
include "wcel.mm"
include "anass.mm"
include "wb.mm"
include "lcfl1lem.mm"
include "anbi1i.mm"
include "bicomi.mm"
include "a1i.mm"
include "syl5bbr.mm"
include "rabbidva2.mm"
include "eqtrd.mm"

theorem mapdvalc
  let wph: wff ph
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
  let cO: class O
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  let vs: setvar s
  assume mapdval.h: |- H = ( LHyp ` K )
  assume mapdval.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval.s: |- S = ( LSubSp ` U )
  assume mapdval.f: |- F = ( LFnl ` U )
  assume mapdval.l: |- L = ( LKer ` U )
  assume mapdval.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdval.k: |- ( ph -> ( K e. X /\ W e. H ) )
  assume mapdval.t: |- ( ph -> T e. S )
  assume mapdvalc.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }

  disjoint K f
  disjoint F f
  disjoint W f
  disjoint f g
  disjoint F g
  disjoint L g
  disjoint O g
  disjoint T f
  disjoint f ph
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f s
  disjoint f w
  disjoint k s
  disjoint K k
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint F w
  disjoint L w
  disjoint O w
  disjoint S s
  disjoint S w
  disjoint W s
  disjoint W w
  disjoint g s
  disjoint F s
  disjoint L s
  disjoint O s
  disjoint T s
  assert |- ( ph -> ( M ` T ) = { f e. C | ( O ` ( L ` f ) ) C_ T } )

  proof
    wph
    cT
    cM
    cfv
    vf
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    @1
    wceq
    #
    @2
    cT
    wss
    #
    wa
    #
    vf
    cF
    crab
    @4
    vf
    cC
    crab
    wph
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
    cX
    mapdval.h
    mapdval.u
    mapdval.s
    mapdval.f
    mapdval.l
    mapdval.o
    mapdval.m
    mapdval.k
    mapdval.t
    mapdval
    wph
    @5
    @4
    vf
    cF
    cC
    @0
    cF
    wcel
    #
    @5
    wa
    @6
    @3
    wa
    #
    @4
    wa
    #
    wph
    @0
    cC
    wcel
    #
    @4
    wa
    #
    @6
    @3
    @4
    anass
    @8
    @10
    wb
    wph
    @10
    @8
    @9
    @7
    @4
    cC
    vg
    cF
    @0
    cL
    cO
    mapdvalc.c
    lcfl1lem
    anbi1i
    bicomi
    a1i
    syl5bbr
    rabbidva2
    eqtrd
end
