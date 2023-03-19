include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cin.mm"
include "wceq.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "lspdisjb.mm"
include "mpbird.mm"

theorem mapdh6b0N
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let cG: class G
  let vw: setvar w
  let cE: class E
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.h: |- H = ( LHyp ` K )
  assume mapdh.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh.v: |- V = ( Base ` U )
  assume mapdh.s: |- .- = ( -g ` U )
  assume mapdhc.o: |- .0. = ( 0g ` U )
  assume mapdh.n: |- N = ( LSpan ` U )
  assume mapdh.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh.d: |- D = ( Base ` C )
  assume mapdh.r: |- R = ( -g ` C )
  assume mapdh.j: |- J = ( LSpan ` C )
  assume mapdh.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhc.f: |- ( ph -> F e. D )
  assume mapdh.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdhcl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh.p: |- .+ = ( +g ` U )
  assume mapdh.a: |- .+b = ( +g ` C )
  assume mapdh6b0.y: |- ( ph -> Y e. V )
  assume mapdh6b0.z: |- ( ph -> Z e. V )
  assume mapdh6b0.ne: |- ( ph -> ( ( N ` { X } ) i^i ( N ` { Y , Z } ) ) = { .0. } )

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
  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint U h
  disjoint .- h
  disjoint Z h
  disjoint Z x
  disjoint G h
  disjoint h w
  disjoint G x
  disjoint E h
  assert |- ( ph -> -. X e. ( N ` { Y , Z } ) )

  proof
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    #
    wcel
    wn
    cX
    csn
    cN
    cfv
    @0
    cin
    c.0
    csn
    wceq
    mapdh6b0.ne
    wph
    cU
    clss
    cfv
    #
    @0
    cN
    cV
    cU
    cX
    c.0
    mapdh.v
    mapdhc.o
    mapdh.n
    @1
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlvec
    wph
    @1
    cN
    cV
    cU
    cY
    cZ
    mapdh.v
    @2
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    mapdh6b0.y
    mapdh6b0.z
    lspprcl
    mapdhcl.x
    lspdisjb
    mpbird
end
