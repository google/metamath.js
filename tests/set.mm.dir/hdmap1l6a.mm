include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "hdmap1l6lem2.mm"
include "oveq12d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "hdmap1l6lem1.mm"
include "oveq2d.mm"
include "wcel.mm"
include "wne.mm"
include "cdif.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lmodindp1.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lcdlmod.mm"
include "cpr.mm"
include "wn.mm"
include "dvhlvec.mm"
include "lspindp2.mm"
include "simpld.mm"
include "hdmap1cl.mm"
include "lspindp1.mm"
include "wss.mm"
include "clss.mm"
include "eqid.mm"
include "lspprcl.mm"
include "lspprvacl.mm"
include "lspsnel5a.mm"
include "lspsnel5.mm"
include "mtbid.mm"
include "nssne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "hdmap1eq.mm"
include "mpbir2and.mm"

theorem hdmap1l6a
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
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
  assume hdmap1l6e.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1l6e.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume hdmap1l6e.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1l6.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume hdmap1l6.fg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume hdmap1l6.fe: |- ( ph -> ( I ` <. X , F , Z >. ) = E )


  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
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
    wceq
    @0
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @3
    csn
    #
    cL
    cfv
    #
    wceq
    cX
    @0
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    #
    cF
    @3
    cR
    co
    #
    csn
    #
    cL
    cfv
    #
    wceq
    wph
    @5
    cG
    cE
    c.pb
    co
    #
    csn
    #
    cL
    cfv
    @7
    wph
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cE
    cF
    cG
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
    hdmap1l6e.y
    hdmap1l6e.z
    hdmap1l6e.xn
    hdmap1l6.yz
    hdmap1l6.fg
    hdmap1l6.fe
    hdmap1l6lem2
    wph
    @6
    @13
    cL
    wph
    @3
    @12
    wph
    @1
    cG
    @2
    cE
    c.pb
    hdmap1l6.fg
    hdmap1l6.fe
    oveq12d
    #
    sneqd
    fveq2d
    eqtr4d
    wph
    @8
    cF
    @12
    cR
    co
    #
    csn
    #
    cL
    cfv
    @11
    wph
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cE
    cF
    cG
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
    hdmap1l6e.y
    hdmap1l6e.z
    hdmap1l6e.xn
    hdmap1l6.yz
    hdmap1l6.fg
    hdmap1l6.fe
    hdmap1l6lem1
    wph
    @10
    @16
    cL
    wph
    @9
    @15
    wph
    @3
    @12
    cF
    cR
    @14
    oveq2d
    sneqd
    fveq2d
    eqtr4d
    wph
    cC
    cD
    cR
    cU
    cF
    @3
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
    @0
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.r
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6cl.x
    hdmap1l6.f
    wph
    @0
    cV
    wcel
    #
    @0
    c.0
    wne
    @0
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
    cY
    cV
    wcel
    cZ
    cV
    wcel
    @17
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
    cY
    cV
    @18
    hdmap1l6e.y
    eldifad
    #
    wph
    cZ
    cV
    @18
    hdmap1l6e.z
    eldifad
    #
    c.pl
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    hdmap1l6.p
    lmodvacl
    syl3anc
    wph
    c.pl
    cN
    cV
    cU
    cY
    cZ
    c.0
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
    @19
    @20
    @21
    hdmap1l6.yz
    lmodindp1
    @0
    cV
    c.0
    eldifsn
    sylanbrc
    wph
    cC
    clmod
    wcel
    @1
    cD
    wcel
    @2
    cD
    wcel
    @3
    cD
    wcel
    wph
    cC
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.c
    hdmap1l6.k
    lcdlmod
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
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    wne
    cZ
    cX
    cY
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cY
    cZ
    c.0
    cX
    hdmap1l6.v
    hdmap1l6c.o
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
    @20
    hdmap1l6e.z
    wph
    cX
    cV
    @18
    hdmap1l6cl.x
    eldifad
    #
    hdmap1l6.yz
    hdmap1l6e.xn
    lspindp2
    simpld
    hdmap1l6cl.x
    @20
    hdmap1cl
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
    @22
    cZ
    csn
    cN
    cfv
    wne
    cY
    cX
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cY
    cZ
    c.0
    cX
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    @23
    hdmap1l6e.y
    @21
    @24
    hdmap1l6.yz
    hdmap1l6e.xn
    lspindp1
    simpld
    hdmap1l6cl.x
    @21
    hdmap1cl
    c.pb
    cD
    cC
    @1
    @2
    hdmap1l6.d
    hdmap1l6.a
    lmodvacl
    syl3anc
    wph
    @4
    @22
    wph
    @4
    cY
    cZ
    cpr
    cN
    cfv
    #
    wss
    @22
    @25
    wss
    #
    wn
    @4
    @22
    wne
    wph
    cU
    clss
    cfv
    #
    @25
    cN
    cU
    @0
    @27
    eqid
    #
    hdmap1l6.n
    @19
    wph
    @27
    cN
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    @28
    hdmap1l6.n
    @19
    @20
    @21
    lspprcl
    #
    wph
    c.pl
    cN
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.n
    @19
    @20
    @21
    lspprvacl
    lspsnel5a
    wph
    cX
    @25
    wcel
    @26
    hdmap1l6e.xn
    wph
    @27
    @25
    cN
    cV
    cU
    cX
    hdmap1l6.v
    @28
    hdmap1l6.n
    @19
    @29
    @24
    lspsnel5
    mtbid
    @4
    @22
    @25
    nssne2
    syl2anc
    necomd
    hdmap1l6.mn
    hdmap1eq
    mpbir2and
end
