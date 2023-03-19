include "co.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "cpr.mm"
include "clsm.mm"
include "eqid.mm"
include "lcfrlem23.mm"
include "cin.mm"
include "lcfrlem24.mm"
include "cvsca.mm"
include "cmulr.mm"
include "clfn.mm"
include "dvhlvec.mm"
include "cv.mm"
include "crab.mm"
include "c0g.mm"
include "lcfrlem10.mm"
include "clss.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lcfrlem22.mm"
include "lsatlssel.mm"
include "lssel.mm"
include "syl2anc.mm"
include "lcfrlem2.mm"
include "eqsstrd.mm"
include "lcfrlem28.mm"
include "lsatel.mm"
include "clmod.mm"
include "lcfrlem30.mm"
include "lkrlss.mm"
include "lcfrlem3.mm"
include "lspsnel5a.mm"
include "csubg.mm"
include "wa.mm"
include "wb.mm"
include "lsssssubg.mm"
include "syl.mm"
include "chlt.mm"
include "eldifad.mm"
include "prssi.mm"
include "dochlss.mm"
include "sseldd.mm"
include "lsmlub.mm"
include "syl3anc.mm"
include "mpbi2and.mm"
include "eqsstr3d.mm"
include "clsh.mm"
include "lcfrlem17.mm"
include "dochsnshp.mm"
include "wne.mm"
include "lcfrlem34.mm"
include "lduallkr3.mm"
include "mpbird.mm"
include "lshpcmp.mm"
include "mpbid.mm"

theorem lcfrlem35
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  assume lcfrlem17.h: |- H = ( LHyp ` K )
  assume lcfrlem17.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem17.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem17.v: |- V = ( Base ` U )
  assume lcfrlem17.p: |- .+ = ( +g ` U )
  assume lcfrlem17.z: |- .0. = ( 0g ` U )
  assume lcfrlem17.n: |- N = ( LSpan ` U )
  assume lcfrlem17.a: |- A = ( LSAtoms ` U )
  assume lcfrlem17.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem17.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfrlem17.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfrlem17.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lcfrlem22.b: |- B = ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) )
  assume lcfrlem24.t: |- .x. = ( .s ` U )
  assume lcfrlem24.s: |- S = ( Scalar ` U )
  assume lcfrlem24.q: |- Q = ( 0g ` S )
  assume lcfrlem24.r: |- R = ( Base ` S )
  assume lcfrlem24.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcfrlem24.ib: |- ( ph -> I e. B )
  assume lcfrlem24.l: |- L = ( LKer ` U )
  assume lcfrlem25.d: |- D = ( LDual ` U )
  assume lcfrlem28.jn: |- ( ph -> ( ( J ` Y ) ` I ) =/= Q )
  assume lcfrlem29.i: |- F = ( invr ` S )
  assume lcfrlem30.m: |- .- = ( -g ` D )
  assume lcfrlem30.c: |- C = ( ( J ` X ) .- ( ( ( F ` ( ( J ` Y ) ` I ) ) ( .r ` S ) ( ( J ` X ) ` I ) ) ( .s ` D ) ( J ` Y ) ) )

  disjoint k v
  disjoint k w
  disjoint k x
  disjoint ._|_ k
  disjoint v w
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint S k
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint V v
  disjoint V x
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint .0. x
  disjoint J f
  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  disjoint R f
  disjoint .x. f
  disjoint U f
  disjoint V f
  disjoint X f
  disjoint Y f
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  assert |- ( ph -> ( ._|_ ` { ( X .+ Y ) } ) = ( L ` C ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    csn
    c.pe
    cfv
    #
    cC
    cL
    cfv
    #
    wss
    @1
    @2
    wceq
    wph
    @1
    cX
    cY
    cpr
    #
    c.pe
    cfv
    #
    cB
    cU
    clsm
    cfv
    #
    co
    #
    @2
    wph
    cA
    cB
    c.pl
    @5
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    @5
    eqid
    #
    lcfrlem23
    wph
    @4
    @2
    wss
    #
    cB
    @2
    wss
    #
    @6
    @2
    wss
    #
    wph
    @4
    cX
    cJ
    cfv
    #
    cL
    cfv
    cY
    cJ
    cfv
    #
    cL
    cfv
    cin
    @2
    wph
    vx
    vw
    vv
    cA
    cB
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cH
    cI
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    lcfrlem24.ib
    lcfrlem24.l
    lcfrlem24
    wph
    cD
    cS
    cD
    cvsca
    cfv
    #
    cS
    cmulr
    cfv
    #
    cU
    @11
    cU
    clfn
    cfv
    #
    @12
    cC
    cF
    cL
    c.mi
    cV
    cI
    cQ
    lcfrlem17.v
    lcfrlem24.s
    @14
    eqid
    #
    lcfrlem24.q
    lcfrlem29.i
    @15
    eqid
    #
    lcfrlem25.d
    @13
    eqid
    #
    lcfrlem30.m
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlvec
    #
    wph
    vx
    vw
    vv
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @20
    wceq
    vf
    @15
    crab
    #
    cD
    c.pl
    cD
    c0g
    cfv
    #
    cR
    cS
    c.x
    cU
    vf
    vk
    @15
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @17
    lcfrlem24.l
    lcfrlem25.d
    @22
    eqid
    #
    @21
    eqid
    #
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem10
    #
    wph
    vx
    vw
    vv
    @21
    cD
    c.pl
    @22
    cR
    cS
    c.x
    cU
    vf
    vk
    @15
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @17
    lcfrlem24.l
    lcfrlem25.d
    @23
    @24
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    #
    wph
    cB
    cU
    clss
    cfv
    #
    wcel
    cI
    cB
    wcel
    cI
    cV
    wcel
    wph
    cA
    @27
    cB
    cU
    @27
    eqid
    #
    lcfrlem17.a
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    #
    wph
    cA
    cB
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem22
    #
    lsatlssel
    #
    lcfrlem24.ib
    @27
    cB
    cV
    cU
    cI
    lcfrlem17.v
    @28
    lssel
    syl2anc
    #
    lcfrlem28.jn
    lcfrlem30.c
    lcfrlem24.l
    lcfrlem2
    eqsstrd
    wph
    cB
    cI
    csn
    cN
    cfv
    @2
    wph
    cA
    cB
    cN
    cU
    cI
    c.0
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    @19
    @30
    lcfrlem24.ib
    wph
    vx
    vw
    vv
    cA
    cB
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cH
    cI
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    lcfrlem24.ib
    lcfrlem24.l
    lcfrlem25.d
    lcfrlem28.jn
    lcfrlem28
    lsatel
    wph
    @27
    @2
    cN
    cU
    cI
    @28
    lcfrlem17.n
    @29
    wph
    cU
    clmod
    wcel
    #
    cC
    @15
    wcel
    @2
    @27
    wcel
    @29
    wph
    vx
    vw
    vv
    cA
    cB
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cF
    cH
    cI
    cJ
    cK
    cL
    c.mi
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    lcfrlem24.ib
    lcfrlem24.l
    lcfrlem25.d
    lcfrlem28.jn
    lcfrlem29.i
    lcfrlem30.m
    lcfrlem30.c
    lcfrlem30
    #
    @27
    @15
    cC
    cL
    cU
    @17
    lcfrlem24.l
    @28
    lkrlss
    syl2anc
    #
    wph
    cD
    cS
    @13
    @14
    cU
    @11
    @15
    @12
    cC
    cF
    cL
    c.mi
    cV
    cI
    cQ
    lcfrlem17.v
    lcfrlem24.s
    @16
    lcfrlem24.q
    lcfrlem29.i
    @17
    lcfrlem25.d
    @18
    lcfrlem30.m
    @19
    @25
    @26
    @32
    lcfrlem28.jn
    lcfrlem30.c
    lcfrlem24.l
    lcfrlem3
    lspsnel5a
    eqsstrd
    wph
    @4
    cU
    csubg
    cfv
    #
    wcel
    cB
    @36
    wcel
    @2
    @36
    wcel
    @8
    @9
    wa
    @10
    wb
    wph
    @27
    @36
    @4
    wph
    @33
    @27
    @36
    wss
    @29
    @27
    cU
    @28
    lsssssubg
    syl
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    cV
    wss
    #
    @4
    @27
    wcel
    lcfrlem17.k
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @38
    wph
    cX
    cV
    c.0
    csn
    #
    lcfrlem17.x
    eldifad
    wph
    cY
    cV
    @39
    lcfrlem17.y
    eldifad
    cX
    cY
    cV
    prssi
    syl2anc
    @27
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    @28
    lcfrlem17.o
    dochlss
    syl2anc
    sseldd
    wph
    @27
    @36
    cB
    @37
    @31
    sseldd
    wph
    @27
    @36
    @2
    @37
    @35
    sseldd
    @5
    @4
    cB
    @2
    cU
    @7
    lsmlub
    syl3anc
    mpbi2and
    eqsstr3d
    wph
    @1
    @2
    cU
    clsh
    cfv
    #
    cU
    @40
    eqid
    #
    @19
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    @40
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.z
    @41
    lcfrlem17.k
    wph
    cA
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem17
    dochsnshp
    wph
    @2
    @40
    wcel
    cC
    @22
    wne
    wph
    vx
    vw
    vv
    cA
    cB
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cF
    cH
    cI
    cJ
    cK
    cL
    c.mi
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    lcfrlem24.ib
    lcfrlem24.l
    lcfrlem25.d
    lcfrlem28.jn
    lcfrlem29.i
    lcfrlem30.m
    lcfrlem30.c
    lcfrlem34
    wph
    cD
    @15
    cC
    @40
    cL
    cU
    @22
    @41
    @17
    lcfrlem24.l
    lcfrlem25.d
    @23
    @19
    @34
    lduallkr3
    mpbird
    lshpcmp
    mpbid
end
