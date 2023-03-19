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
include "inss2.mm"
include "syl6eqss.mm"
include "dvhlvec.mm"
include "lcfrlem22.mm"
include "lsatel.mm"
include "clss.mm"
include "dvhlmod.mm"
include "clmod.mm"
include "wcel.mm"
include "clfn.mm"
include "cv.mm"
include "crab.mm"
include "c0g.mm"
include "lcfrlem10.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "lsatssv.mm"
include "sseldd.mm"
include "ellkr2.mm"
include "mpbird.mm"
include "lspsnel5a.mm"
include "eqsstrd.mm"
include "csubg.mm"
include "wa.mm"
include "wb.mm"
include "lsssssubg.mm"
include "syl.mm"
include "chlt.mm"
include "eldifad.mm"
include "prssi.mm"
include "dochlss.mm"
include "lspprcl.mm"
include "lcfrlem17.mm"
include "snssd.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "eqsstr3d.mm"
include "clsh.mm"
include "dochsnshp.mm"
include "wne.mm"
include "cdif.mm"
include "lcfrlem13.mm"
include "eldifsni.mm"
include "lduallkr3.mm"
include "lshpcmp.mm"
include "mpbid.mm"

theorem lcfrlem25
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
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
  assume lcfrlem25.jz: |- ( ph -> ( ( J ` Y ) ` I ) = Q )
  assume lcfrlem25.in: |- ( ph -> I =/= .0. )

  disjoint k v
  disjoint k w
  disjoint k x
  disjoint v w
  disjoint v x
  disjoint w x
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
  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  disjoint R f
  disjoint .x. f
  disjoint U f
  disjoint V f
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  assert |- ( ph -> ( ._|_ ` { ( X .+ Y ) } ) = ( L ` ( J ` Y ) ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    csn
    #
    c.pe
    cfv
    #
    cY
    cJ
    cfv
    #
    cL
    cfv
    #
    wss
    @2
    @4
    wceq
    wph
    @2
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
    @4
    wph
    cA
    cB
    c.pl
    @7
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
    @7
    eqid
    #
    lcfrlem23
    wph
    @6
    @4
    wss
    #
    cB
    @4
    wss
    #
    @8
    @4
    wss
    #
    wph
    @6
    cX
    cJ
    cfv
    cL
    cfv
    #
    @4
    cin
    @4
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
    @13
    @4
    inss2
    syl6eqss
    wph
    cB
    cI
    csn
    cN
    cfv
    @4
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
    lcfrlem24.ib
    lcfrlem25.in
    lsatel
    wph
    cU
    clss
    cfv
    #
    @4
    cN
    cU
    cI
    @16
    eqid
    #
    lcfrlem17.n
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
    cU
    clmod
    wcel
    #
    @3
    cU
    clfn
    cfv
    #
    wcel
    @4
    @16
    wcel
    @18
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
    @21
    wceq
    vf
    @20
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
    @20
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
    @20
    eqid
    #
    lcfrlem24.l
    lcfrlem25.d
    @23
    eqid
    #
    @22
    eqid
    #
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    #
    @16
    @20
    @3
    cL
    cU
    @24
    lcfrlem24.l
    @17
    lkrlss
    syl2anc
    #
    wph
    cI
    @4
    wcel
    cI
    @3
    cfv
    cQ
    wceq
    lcfrlem25.jz
    wph
    cS
    @20
    @3
    cL
    cV
    cU
    cI
    clmod
    cQ
    lcfrlem17.v
    lcfrlem24.s
    lcfrlem24.q
    @24
    lcfrlem24.l
    @18
    @27
    wph
    cB
    cV
    cI
    wph
    cA
    cB
    cV
    cU
    lcfrlem17.v
    lcfrlem17.a
    @18
    @15
    lsatssv
    lcfrlem24.ib
    sseldd
    ellkr2
    mpbird
    lspsnel5a
    eqsstrd
    wph
    @6
    cU
    csubg
    cfv
    #
    wcel
    cB
    @29
    wcel
    @4
    @29
    wcel
    @10
    @11
    wa
    @12
    wb
    wph
    @16
    @29
    @6
    wph
    @19
    @16
    @29
    wss
    @18
    @16
    cU
    @17
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
    #
    @5
    cV
    wss
    #
    @6
    @16
    wcel
    lcfrlem17.k
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @32
    wph
    cX
    cV
    c.0
    csn
    #
    lcfrlem17.x
    eldifad
    #
    wph
    cY
    cV
    @33
    lcfrlem17.y
    eldifad
    #
    cX
    cY
    cV
    prssi
    syl2anc
    @16
    cU
    cH
    cK
    c.pe
    cV
    cW
    @5
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    @17
    lcfrlem17.o
    dochlss
    syl2anc
    sseldd
    wph
    @16
    @29
    cB
    @30
    wph
    cB
    @5
    cN
    cfv
    #
    @2
    cin
    #
    @16
    lcfrlem22.b
    wph
    @19
    @36
    @16
    wcel
    @2
    @16
    wcel
    #
    @37
    @16
    wcel
    @18
    wph
    @16
    cN
    cV
    cU
    cX
    cY
    lcfrlem17.v
    @17
    lcfrlem17.n
    @18
    @34
    @35
    lspprcl
    wph
    @31
    @1
    cV
    wss
    @38
    lcfrlem17.k
    wph
    @0
    cV
    wph
    @0
    cV
    @33
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
    #
    eldifad
    snssd
    @16
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    @17
    lcfrlem17.o
    dochlss
    syl2anc
    @16
    @36
    @2
    cU
    @17
    lssincl
    syl3anc
    syl5eqel
    sseldd
    wph
    @16
    @29
    @4
    @30
    @28
    sseldd
    @7
    @6
    cB
    @4
    cU
    @9
    lsmlub
    syl3anc
    mpbi2and
    eqsstr3d
    wph
    @2
    @4
    cU
    clsh
    cfv
    #
    cU
    @40
    eqid
    #
    @14
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
    @39
    dochsnshp
    wph
    @4
    @40
    wcel
    @3
    @23
    wne
    #
    wph
    @3
    @22
    @23
    csn
    cdif
    wcel
    @42
    wph
    vx
    vw
    vv
    @22
    cD
    c.pl
    @23
    cR
    cS
    c.x
    cU
    vf
    vk
    @20
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
    @24
    lcfrlem24.l
    lcfrlem25.d
    @25
    @26
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem13
    @3
    @22
    @23
    eldifsni
    syl
    wph
    cD
    @20
    @3
    @40
    cL
    cU
    @23
    @41
    @24
    lcfrlem24.l
    lcfrlem25.d
    @25
    @14
    @27
    lduallkr3
    mpbird
    lshpcmp
    mpbid
end
