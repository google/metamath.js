include "wceq.mm"
include "clspn.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "lcdlvec.mm"
include "hdmapnzcl.mm"
include "csn.mm"
include "cmpd.mm"
include "wne.mm"
include "clss.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapd11.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "hdmap10.mm"
include "3netr3d.mm"
include "hdmap14lem8.mm"
include "lvecindp2.mm"
include "simpld.mm"
include "simprd.mm"
include "eqtr3d.mm"

theorem hdmap14lem9
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmap14lem8.h: |- H = ( LHyp ` K )
  assume hdmap14lem8.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem8.v: |- V = ( Base ` U )
  assume hdmap14lem8.q: |- .+ = ( +g ` U )
  assume hdmap14lem8.t: |- .x. = ( .s ` U )
  assume hdmap14lem8.o: |- .0. = ( 0g ` U )
  assume hdmap14lem8.n: |- N = ( LSpan ` U )
  assume hdmap14lem8.r: |- R = ( Scalar ` U )
  assume hdmap14lem8.b: |- B = ( Base ` R )
  assume hdmap14lem8.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem8.d: |- .+b = ( +g ` C )
  assume hdmap14lem8.e: |- .xb = ( .s ` C )
  assume hdmap14lem8.p: |- P = ( Scalar ` C )
  assume hdmap14lem8.a: |- A = ( Base ` P )
  assume hdmap14lem8.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem8.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem8.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap14lem8.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap14lem8.f: |- ( ph -> F e. B )
  assume hdmap14lem8.g: |- ( ph -> G e. A )
  assume hdmap14lem8.i: |- ( ph -> I e. A )
  assume hdmap14lem8.xx: |- ( ph -> ( S ` ( F .x. X ) ) = ( G .xb ( S ` X ) ) )
  assume hdmap14lem8.yy: |- ( ph -> ( S ` ( F .x. Y ) ) = ( I .xb ( S ` Y ) ) )
  assume hdmap14lem8.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume hdmap14lem8.j: |- ( ph -> J e. A )
  assume hdmap14lem8.xy: |- ( ph -> ( S ` ( F .x. ( X .+ Y ) ) ) = ( J .xb ( S ` ( X .+ Y ) ) ) )


  assert |- ( ph -> G = I )

  proof
    wph
    cJ
    cG
    cI
    wph
    cJ
    cG
    wceq
    #
    cJ
    cI
    wceq
    #
    wph
    cJ
    cJ
    cG
    cI
    c.pb
    c.xb
    cP
    cA
    cC
    clspn
    cfv
    #
    cC
    cbs
    cfv
    #
    cC
    cX
    cS
    cfv
    #
    cY
    cS
    cfv
    #
    cC
    c0g
    cfv
    #
    @3
    eqid
    #
    hdmap14lem8.d
    hdmap14lem8.p
    hdmap14lem8.a
    hdmap14lem8.e
    @6
    eqid
    #
    @2
    eqid
    #
    wph
    cC
    cH
    cK
    cW
    hdmap14lem8.h
    hdmap14lem8.c
    hdmap14lem8.k
    lcdlvec
    wph
    cC
    @3
    @6
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    c.0
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.o
    hdmap14lem8.c
    @8
    @7
    hdmap14lem8.s
    hdmap14lem8.k
    hdmap14lem8.x
    hdmapnzcl
    wph
    cC
    @3
    @6
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    c.0
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.o
    hdmap14lem8.c
    @8
    @7
    hdmap14lem8.s
    hdmap14lem8.k
    hdmap14lem8.y
    hdmapnzcl
    hdmap14lem8.j
    hdmap14lem8.j
    hdmap14lem8.g
    hdmap14lem8.i
    wph
    cX
    csn
    cN
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    @11
    cfv
    #
    @4
    csn
    @2
    cfv
    @5
    csn
    @2
    cfv
    wph
    @12
    @14
    wne
    @10
    @13
    wne
    hdmap14lem8.ne
    wph
    @12
    @14
    @10
    @13
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    @11
    cW
    @10
    @13
    hdmap14lem8.h
    hdmap14lem8.u
    @15
    eqid
    #
    @11
    eqid
    #
    hdmap14lem8.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    @10
    @15
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.k
    dvhlmod
    #
    wph
    cX
    cV
    c.0
    csn
    #
    hdmap14lem8.x
    eldifad
    #
    @15
    cN
    cV
    cU
    cX
    hdmap14lem8.v
    @16
    hdmap14lem8.n
    lspsncl
    syl2anc
    wph
    @18
    cY
    cV
    wcel
    @13
    @15
    wcel
    @19
    wph
    cY
    cV
    @20
    hdmap14lem8.y
    eldifad
    #
    @15
    cN
    cV
    cU
    cY
    hdmap14lem8.v
    @16
    hdmap14lem8.n
    lspsncl
    syl2anc
    mapd11
    necon3bid
    mpbird
    wph
    cC
    cS
    cX
    cU
    cH
    cK
    @2
    @11
    cN
    cV
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.n
    hdmap14lem8.c
    @9
    @17
    hdmap14lem8.s
    hdmap14lem8.k
    @21
    hdmap10
    wph
    cC
    cS
    cY
    cU
    cH
    cK
    @2
    @11
    cN
    cV
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.n
    hdmap14lem8.c
    @9
    @17
    hdmap14lem8.s
    hdmap14lem8.k
    @22
    hdmap10
    3netr3d
    wph
    cA
    cB
    cC
    cP
    c.pl
    c.pb
    cR
    cS
    c.xb
    c.x
    cU
    cF
    cG
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.q
    hdmap14lem8.t
    hdmap14lem8.o
    hdmap14lem8.n
    hdmap14lem8.r
    hdmap14lem8.b
    hdmap14lem8.c
    hdmap14lem8.d
    hdmap14lem8.e
    hdmap14lem8.p
    hdmap14lem8.a
    hdmap14lem8.s
    hdmap14lem8.k
    hdmap14lem8.x
    hdmap14lem8.y
    hdmap14lem8.f
    hdmap14lem8.g
    hdmap14lem8.i
    hdmap14lem8.xx
    hdmap14lem8.yy
    hdmap14lem8.ne
    hdmap14lem8.j
    hdmap14lem8.xy
    hdmap14lem8
    lvecindp2
    #
    simpld
    wph
    @0
    @1
    @23
    simprd
    eqtr3d
end
