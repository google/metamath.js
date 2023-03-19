include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cdif.mm"
include "mapdhval.mm"
include "wcel.mm"
include "wn.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalse.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem mapdhval2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let vh: setvar h
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh2.x: |- ( ph -> X e. A )
  assume mapdh2.f: |- ( ph -> F e. B )
  assume mapdh2.y: |- ( ph -> Y e. ( V \ { .0. } ) )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  disjoint .0. h
  assert |- ( ph -> ( I ` <. X , F , Y >. ) = ( iota_ h e. D ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( F R h ) } ) ) ) )

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
    cQ
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
    cJ
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
    @1
    cR
    co
    csn
    cJ
    cfv
    wceq
    wa
    vh
    cD
    crio
    #
    cif
    #
    @2
    wph
    vx
    cA
    cB
    cC
    cD
    cQ
    cR
    vh
    cV
    c.0
    csn
    cdif
    #
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cX
    cY
    c.0
    mapdh.q
    mapdh.i
    mapdh2.x
    mapdh2.f
    mapdh2.y
    mapdhval
    wph
    cY
    @4
    wcel
    #
    @0
    wn
    @3
    @2
    wceq
    mapdh2.y
    @5
    cY
    c.0
    cY
    cV
    c.0
    eldifsni
    neneqd
    @0
    cQ
    @2
    iffalse
    3syl
    eqtrd
end
