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
include "hdmap1l6a.mm"

theorem hdmap1l6e
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


  assert |- ( ph -> ( I ` <. X , F , ( ( w .+ Y ) .+ Z ) >. ) = ( ( I ` <. X , F , ( w .+ Y ) >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
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
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    @2
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
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    #
    wph
    @1
    cV
    @5
    hdmap1l6d.w
    eldifad
    #
    wph
    cY
    cV
    @5
    hdmap1l6d.y
    eldifad
    #
    c.pl
    cV
    cU
    @1
    cY
    hdmap1l6.v
    hdmap1l6.p
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
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
    @7
    wph
    cX
    cV
    @5
    hdmap1l6cl.x
    eldifad
    #
    @8
    hdmap1l6d.wn
    lspindpi
    simprd
    lmodindp1
    @2
    cV
    c.0
    eldifsn
    sylanbrc
    hdmap1l6d.z
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
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    @13
    hdmap1l6cl.x
    @9
    wph
    cZ
    cV
    @5
    hdmap1l6d.z
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
    @13
    hdmap1l6cl.x
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.yz
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
    hdmap1l6.v
    hdmap1l6.n
    @13
    @14
    @8
    @23
    hdmap1l6d.xn
    lspindpi
    simpld
    #
    hdmap1l6d.wn
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
    @13
    hdmap1l6cl.x
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.yz
    @24
    hdmap1l6d.wn
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
    hdmap1l6.v
    hdmap1l6.n
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
    hdmap1l6a
end
