include "cv.mm"
include "cotp.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "mapdh6gN.mm"
include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "mapdhcl.mm"
include "simprd.mm"
include "lmodass.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "mapdindp1.mm"
include "lmodlcan.mm"
include "mpbid.mm"

theorem mapdh6hN
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
  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cX
    cF
    vw
    cv
    #
    cotp
    cI
    cfv
    #
    cX
    cF
    cY
    cZ
    c.pl
    co
    #
    cotp
    cI
    cfv
    #
    c.pb
    co
    #
    @1
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    c.pb
    co
    #
    c.pb
    co
    #
    wceq
    #
    @3
    @7
    wceq
    #
    wph
    @4
    @1
    @5
    c.pb
    co
    @6
    c.pb
    co
    #
    @8
    wph
    vx
    vw
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    vh
    cF
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
    cY
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
    mapdh6d.xn
    mapdh6d.yz
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.wn
    mapdh6gN
    wph
    cC
    clmod
    wcel
    #
    @1
    cD
    wcel
    #
    @5
    cD
    wcel
    #
    @6
    cD
    wcel
    #
    @11
    @8
    wceq
    wph
    cC
    cH
    cK
    cW
    mapdh.h
    mapdh.c
    mapdh.k
    lcdlmod
    #
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
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
    @0
    c.0
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
    wph
    @0
    cV
    c.0
    csn
    #
    mapdh6d.w
    eldifad
    #
    wph
    @0
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    wph
    @19
    @20
    wne
    @19
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
    @0
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
    @18
    wph
    cX
    cV
    @17
    mapdhcl.x
    eldifad
    #
    wph
    cY
    cV
    @17
    mapdh6d.y
    eldifad
    #
    mapdh6d.wn
    lspindpi
    simpld
    necomd
    mapdhcl
    #
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
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
    cY
    c.0
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
    @24
    wph
    @20
    @21
    wne
    #
    @20
    cZ
    csn
    cN
    cfv
    wne
    #
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    mapdh.v
    mapdh.n
    @22
    @23
    @24
    wph
    cZ
    cV
    @17
    mapdh6d.z
    eldifad
    #
    mapdh6d.xn
    lspindpi
    #
    simpld
    #
    mapdhcl
    #
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
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
    cZ
    c.0
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
    @28
    wph
    @26
    @27
    @29
    simprd
    mapdhcl
    #
    c.pb
    cD
    cC
    @1
    @5
    @6
    mapdh.d
    mapdh.a
    lmodass
    syl13anc
    eqtrd
    wph
    @12
    @3
    cD
    wcel
    @7
    cD
    wcel
    #
    @13
    @9
    @10
    wb
    @16
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
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
    wph
    cU
    clmod
    wcel
    cY
    cV
    wcel
    cZ
    cV
    wcel
    @2
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    @24
    @28
    c.pl
    cV
    cU
    cY
    cZ
    mapdh.v
    mapdh.p
    lmodvacl
    syl3anc
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
    @22
    mapdhcl.x
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.yz
    @30
    mapdh6d.wn
    mapdindp1
    mapdhcl
    wph
    @12
    @14
    @15
    @33
    @16
    @31
    @32
    c.pb
    cD
    cC
    @5
    @6
    mapdh.d
    mapdh.a
    lmodvacl
    syl3anc
    @25
    c.pb
    cD
    cC
    @3
    @7
    @1
    mapdh.d
    mapdh.a
    lmodlcan
    syl13anc
    mpbid
end
