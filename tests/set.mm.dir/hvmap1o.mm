include "csn.mm"
include "cdif.mm"
include "wf1o.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "csca.mm"
include "cbs.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "lcf1o.mm"
include "wb.mm"
include "chlt.mm"
include "hvmapfval.mm"
include "f1oeq1.mm"
include "syl.mm"
include "mpbird.mm"

theorem hvmap1o
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
  assert |- ( ph -> M : ( V \ { .0. } ) -1-1-onto-> ( C \ { Q } ) )

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
    cM
    wf1o
    #
    @0
    @1
    vx
    @0
    vv
    cV
    vv
    cv
    vw
    cv
    vk
    cv
    vx
    cv
    #
    cU
    cvsca
    cfv
    #
    co
    cU
    cplusg
    cfv
    #
    co
    wceq
    vw
    @3
    csn
    cO
    cfv
    wrex
    vk
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    crio
    cmpt
    cmpt
    #
    wf1o
    #
    wph
    vx
    vw
    vv
    cC
    cD
    @5
    cQ
    @7
    @6
    @4
    cU
    vf
    vk
    cF
    cH
    @8
    cK
    cL
    cO
    cV
    cW
    c.0
    hvmap1o.h
    hvmap1o.o
    hvmap1o.u
    hvmap1o.v
    @5
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    #
    hvmap1o.z
    hvmap1o.f
    hvmap1o.l
    hvmap1o.d
    hvmap1o.q
    hvmap1o.c
    @8
    eqid
    hvmap1o.k
    lcf1o
    wph
    cM
    @8
    wceq
    @2
    @9
    wb
    wph
    vx
    vv
    vw
    chlt
    @5
    @7
    @6
    @4
    cU
    vk
    cH
    cK
    cM
    cO
    cV
    cW
    c.0
    hvmap1o.h
    hvmap1o.u
    hvmap1o.o
    hvmap1o.v
    @10
    @11
    hvmap1o.z
    @12
    @13
    hvmap1o.m
    hvmap1o.k
    hvmapfval
    @0
    @1
    cM
    @8
    f1oeq1
    syl
    mpbird
end
