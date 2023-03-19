include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "chlt.mm"
include "eqid.mm"
include "eldifad.mm"
include "hdmap1val.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalse.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem hdmap1val2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmap1val2.h: |- H = ( LHyp ` K )
  assume hdmap1val2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1val2.v: |- V = ( Base ` U )
  assume hdmap1val2.s: |- .- = ( -g ` U )
  assume hdmap1val2.o: |- .0. = ( 0g ` U )
  assume hdmap1val2.n: |- N = ( LSpan ` U )
  assume hdmap1val2.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1val2.d: |- D = ( Base ` C )
  assume hdmap1val2.r: |- R = ( -g ` C )
  assume hdmap1val2.l: |- L = ( LSpan ` C )
  assume hdmap1val2.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1val2.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1val2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1val2.x: |- ( ph -> X e. V )
  assume hdmap1val2.f: |- ( ph -> F e. D )
  assume hdmap1val2.y: |- ( ph -> Y e. ( V \ { .0. } ) )

  disjoint C h
  disjoint D h
  disjoint F h
  disjoint L h
  disjoint M h
  disjoint N h
  disjoint U h
  disjoint V h
  disjoint X h
  disjoint Y h
  disjoint h ph
  assert |- ( ph -> ( I ` <. X , F , Y >. ) = ( iota_ h e. D ( ( M ` ( N ` { Y } ) ) = ( L ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( L ` { ( F R h ) } ) ) ) )

  proof
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    cY
    c.0
    wceq
    #
    cC
    c0g
    cfv
    #
    cY
    csn
    cN
    cfv
    cM
    cfv
    vh
    cv
    #
    csn
    cL
    cfv
    wceq
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    @2
    cR
    co
    csn
    cL
    cfv
    wceq
    wa
    vh
    cD
    crio
    #
    cif
    #
    @3
    wph
    chlt
    cC
    cD
    @1
    cR
    cU
    vh
    cF
    cH
    cI
    cL
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1val2.h
    hdmap1val2.u
    hdmap1val2.v
    hdmap1val2.s
    hdmap1val2.o
    hdmap1val2.n
    hdmap1val2.c
    hdmap1val2.d
    hdmap1val2.r
    @1
    eqid
    hdmap1val2.l
    hdmap1val2.m
    hdmap1val2.i
    hdmap1val2.k
    hdmap1val2.x
    hdmap1val2.f
    wph
    cY
    cV
    c.0
    csn
    #
    hdmap1val2.y
    eldifad
    hdmap1val
    wph
    cY
    cV
    @5
    cdif
    wcel
    #
    @0
    wn
    @4
    @3
    wceq
    hdmap1val2.y
    @6
    cY
    c.0
    cY
    cV
    c.0
    eldifsni
    neneqd
    @0
    @1
    @3
    iffalse
    3syl
    eqtrd
end
