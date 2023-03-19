include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cvv.mm"
include "wcel.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "mapdhval.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem mapdhval0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cY: class Y
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh0.o: |- .0. = ( 0g ` U )
  assume mapdh0.x: |- ( ph -> X e. A )
  assume mapdh0.f: |- ( ph -> F e. B )

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
  disjoint h ph
  disjoint .0. h
  disjoint Y h
  disjoint Y x
  assert |- ( ph -> ( I ` <. X , F , .0. >. ) = Q )

  proof
    wph
    cX
    cF
    c.0
    cotp
    cI
    cfv
    c.0
    c.0
    wceq
    #
    cQ
    c.0
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
    c.0
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
    cQ
    wph
    vx
    cA
    cB
    cC
    cD
    cQ
    cR
    vh
    cvv
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cX
    c.0
    c.0
    mapdh.q
    mapdh.i
    mapdh0.x
    mapdh0.f
    c.0
    cvv
    wcel
    wph
    c.0
    cU
    c0g
    cfv
    cvv
    mapdh0.o
    cU
    c0g
    fvex
    eqeltri
    a1i
    mapdhval
    @0
    cQ
    @2
    c.0
    eqid
    iftruei
    syl6eq
end
