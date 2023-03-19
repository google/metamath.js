include "csn.mm"
include "cdif.mm"
include "wf1o.mm"
include "wf.mm"
include "hvmap1o.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnd.mm"

theorem hvmapclN
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  assume hvmap1o.h: |- H = ( LHyp ` K )
  assume hvmap1o.o: |- O = ( ( ocH ` K ) ` W )
  assume hvmap1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmap1o.v: |- V = ( Base ` U )
  assume hvmap1o.z: |- .0. = ( 0g ` U )
  assume hvmap1o.f: |- F = ( LFnl ` U )
  assume hvmap1o.l: |- L = ( LKer ` U )
  assume hvmap1o.d: |- D = ( LDual ` U )
  assume hvmap1o.q: |- Q = ( 0g ` D )
  assume hvmap1o.c: |- C = { f e. F | ( O ` ( O ` ( L ` f ) ) ) = ( L ` f ) }
  assume hvmap1o.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmap1o.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hvmapcl.x: |- ( ph -> X e. ( V \ { .0. } ) )

  disjoint F f
  disjoint L f
  disjoint O f
  disjoint U f
  disjoint V f
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint K k
  disjoint v w
  disjoint v x
  disjoint K v
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint O k
  disjoint O v
  disjoint O w
  disjoint O x
  disjoint U k
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint V v
  disjoint V x
  disjoint W k
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint .0. x
  assert |- ( ph -> ( M ` X ) e. ( C \ { Q } ) )

  proof
    wph
    cV
    c.0
    csn
    cdif
    #
    cC
    cQ
    csn
    cdif
    #
    cX
    cM
    wph
    @0
    @1
    cM
    wf1o
    @0
    @1
    cM
    wf
    wph
    cC
    cD
    cQ
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cV
    cW
    c.0
    hvmap1o.h
    hvmap1o.o
    hvmap1o.u
    hvmap1o.v
    hvmap1o.z
    hvmap1o.f
    hvmap1o.l
    hvmap1o.d
    hvmap1o.q
    hvmap1o.c
    hvmap1o.m
    hvmap1o.k
    hvmap1o
    @0
    @1
    cM
    f1of
    syl
    hvmapcl.x
    ffvelrnd
end
