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

theorem hdmap1l6b0N
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
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
  let cZ: class Z
  assume hdmap1l6.h: |- H = ( LHyp ` K )
  assume hdmap1l6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1l6.v: |- V = ( Base ` U )
  assume hdmap1l6.p: |- .+ = ( +g ` U )
  assume hdmap1l6.s: |- .- = ( -g ` U )
  assume hdmap1l6c.o: |- .0. = ( 0g ` U )
  assume hdmap1l6.n: |- N = ( LSpan ` U )
  assume hdmap1l6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1l6.d: |- D = ( Base ` C )
  assume hdmap1l6.a: |- .+b = ( +g ` C )
  assume hdmap1l6.r: |- R = ( -g ` C )
  assume hdmap1l6.q: |- Q = ( 0g ` C )
  assume hdmap1l6.l: |- L = ( LSpan ` C )
  assume hdmap1l6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1l6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1l6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1l6.f: |- ( ph -> F e. D )
  assume hdmap1l6cl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1l6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1l6b0.y: |- ( ph -> Y e. V )
  assume hdmap1l6b0.z: |- ( ph -> Z e. V )
  assume hdmap1l6b0.ne: |- ( ph -> ( ( N ` { X } ) i^i ( N ` { Y , Z } ) ) = { .0. } )


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
    hdmap1l6b0.ne
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
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    @1
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlvec
    wph
    @1
    cN
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    @2
    hdmap1l6.n
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    hdmap1l6b0.y
    hdmap1l6b0.z
    lspprcl
    hdmap1l6cl.x
    lspdisjb
    mpbird
end
