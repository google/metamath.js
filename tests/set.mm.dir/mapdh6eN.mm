include "cotp.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simprd.mm"
include "lmodindp1.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cpr.mm"
include "wn.mm"
include "simpld.mm"
include "mapdindp3.mm"
include "mapdindp4.mm"
include "lspindp1.mm"
include "prcom.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "sylnibr.mm"
include "necomd.mm"
include "eqidd.mm"
include "mapdh6aN.mm"

theorem mapdh6eN
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
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
  assume mapdh6d.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh6d.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume mapdh6d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh6d.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh6d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh6d.wn: |- ( ph -> -. w e. ( N ` { X , Y } ) )

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
  disjoint h w
  disjoint Z h
  disjoint Z x
  disjoint .+b h
  disjoint I h
  disjoint I x
  disjoint .+ h
  disjoint .+ x
  disjoint w x
  disjoint G h
  disjoint G x
  disjoint E h
  assert |- ( ph -> ( I ` <. X , F , ( ( w .+ Y ) .+ Z ) >. ) = ( ( I ` <. X , F , ( w .+ Y ) >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    vx
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    vh
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    cF
    cX
    cF
    vw
    cv
    #
    cY
    c.pl
    co
    #
    cotp
    cI
    cfv
    #
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    @2
    c.0
    cZ
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    mapdh.p
    mapdh.a
    wph
    @2
    cV
    wcel
    #
    @2
    c.0
    wne
    @2
    cV
    c.0
    csn
    #
    cdif
    wcel
    wph
    cU
    clmod
    wcel
    @1
    cV
    wcel
    cY
    cV
    wcel
    @4
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    #
    wph
    @1
    cV
    @5
    mapdh6d.w
    eldifad
    #
    wph
    cY
    cV
    @5
    mapdh6d.y
    eldifad
    #
    c.pl
    cV
    cU
    @1
    cY
    mapdh.v
    mapdh.p
    lmodvacl
    syl3anc
    #
    wph
    c.pl
    cN
    cV
    cU
    @1
    cY
    c.0
    mapdh.v
    mapdh.p
    mapdhc.o
    mapdh.n
    @6
    @7
    @8
    wph
    @1
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    wne
    @10
    cY
    csn
    cN
    cfv
    #
    wne
    wph
    cN
    cV
    cU
    @1
    cX
    cY
    mapdh.v
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlvec
    #
    @7
    wph
    cX
    cV
    @5
    mapdhcl.x
    eldifad
    #
    @8
    mapdh6d.wn
    lspindpi
    simprd
    lmodindp1
    @2
    cV
    c.0
    eldifsn
    sylanbrc
    mapdh6d.z
    wph
    cX
    cZ
    @2
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    cX
    @2
    cZ
    cpr
    #
    cN
    cfv
    #
    wcel
    wph
    cZ
    csn
    cN
    cfv
    #
    @2
    csn
    cN
    cfv
    #
    wne
    #
    @17
    wn
    wph
    cN
    cV
    cU
    cX
    @2
    c.0
    cZ
    mapdh.v
    mapdhc.o
    mapdh.n
    @13
    mapdhcl.x
    @9
    wph
    cZ
    cV
    @5
    mapdh6d.z
    eldifad
    #
    wph
    vw
    c.pl
    cN
    cV
    cU
    cX
    cY
    c.0
    cZ
    mapdh.v
    mapdh.p
    mapdhc.o
    mapdh.n
    @13
    mapdhcl.x
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.yz
    wph
    @11
    @12
    wne
    @11
    @20
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    mapdh.v
    mapdh.n
    @13
    @14
    @8
    @23
    mapdh6d.xn
    lspindpi
    simpld
    #
    mapdh6d.wn
    mapdindp3
    wph
    vw
    c.pl
    cN
    cV
    cU
    cX
    cY
    c.0
    cZ
    mapdh.v
    mapdh.p
    mapdhc.o
    mapdh.n
    @13
    mapdhcl.x
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.yz
    @24
    mapdh6d.wn
    mapdindp4
    #
    lspindp1
    simprd
    @19
    @16
    cX
    @18
    @15
    cN
    @2
    cZ
    prcom
    fveq2i
    eleq2i
    sylnibr
    wph
    @20
    @21
    wph
    @20
    @11
    wne
    @22
    wph
    cN
    cV
    cU
    cZ
    cX
    @2
    mapdh.v
    mapdh.n
    @13
    @23
    @14
    @9
    @25
    lspindpi
    simprd
    necomd
    wph
    @3
    eqidd
    wph
    @0
    eqidd
    mapdh6aN
end
