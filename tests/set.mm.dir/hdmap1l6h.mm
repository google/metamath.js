include "cv.mm"
include "cotp.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "hdmap1l6g.mm"
include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "csn.mm"
include "wne.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "hdmap1cl.mm"
include "simprd.mm"
include "lmodass.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "wb.mm"
include "mapdindp1.mm"
include "dvhlmod.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lmodlcan.mm"
include "mpbid.mm"

theorem hdmap1l6h
  let wph: wff ph
  let vw: setvar w
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
  assume hdmap1l6d.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1l6d.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume hdmap1l6d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1l6d.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume hdmap1l6d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume hdmap1l6d.wn: |- ( ph -> -. w e. ( N ` { X , Y } ) )


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
    vw
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6cl.x
    hdmap1l6.mn
    hdmap1l6d.xn
    hdmap1l6d.yz
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.wn
    hdmap1l6g
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
    hdmap1l6.h
    hdmap1l6.c
    hdmap1l6.k
    lcdlmod
    #
    wph
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    @0
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6.mn
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
    @17
    @18
    wne
    @17
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
    hdmap1l6.v
    hdmap1l6.n
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlvec
    #
    wph
    @0
    cV
    c.0
    csn
    #
    hdmap1l6d.w
    eldifad
    #
    wph
    cX
    cV
    @21
    hdmap1l6cl.x
    eldifad
    #
    wph
    cY
    cV
    @21
    hdmap1l6d.y
    eldifad
    #
    hdmap1l6d.wn
    lspindpi
    simpld
    necomd
    hdmap1l6cl.x
    @22
    hdmap1cl
    #
    wph
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6.mn
    wph
    @18
    @19
    wne
    #
    @18
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
    hdmap1l6.v
    hdmap1l6.n
    @20
    @23
    @24
    wph
    cZ
    cV
    @21
    hdmap1l6d.z
    eldifad
    #
    hdmap1l6d.xn
    lspindpi
    #
    simpld
    #
    hdmap1l6cl.x
    @24
    hdmap1cl
    #
    wph
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    cZ
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6.mn
    wph
    @26
    @27
    @29
    simprd
    hdmap1l6cl.x
    @28
    hdmap1cl
    #
    c.pb
    cD
    cC
    @1
    @5
    @6
    hdmap1l6.d
    hdmap1l6.a
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
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    @2
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6.mn
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
    @20
    hdmap1l6cl.x
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.yz
    @30
    hdmap1l6d.wn
    mapdindp1
    hdmap1l6cl.x
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
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    @24
    @28
    c.pl
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    hdmap1l6.p
    lmodvacl
    syl3anc
    hdmap1cl
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
    hdmap1l6.d
    hdmap1l6.a
    lmodvacl
    syl3anc
    @25
    c.pb
    cD
    cC
    @3
    @7
    @1
    hdmap1l6.d
    hdmap1l6.a
    lmodlcan
    syl13anc
    mpbid
end
