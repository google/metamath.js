include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wral.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "adantr.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "syl.mm"
include "sselda.mm"
include "ovresd.mm"
include "syl5eq.mm"
include "cngp.mm"
include "wceq.mm"
include "ccph.mm"
include "cphngp.mm"
include "ngpds.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "w3a.mm"
include "minveclem1.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0red.mm"
include "simp3d.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "infrecl.mm"
include "syl5eqel.mm"
include "resqcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "breq12d.mm"
include "clmod.mm"
include "cphlmod.mm"
include "lmodvsubcl.mm"
include "nmcl.mm"
include "nmge0.mm"
include "wb.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "le2sqd.mm"
include "breq2i.mm"
include "syl5bb.mm"
include "3bitr2d.mm"
include "cmpt.mm"
include "crn.mm"
include "raleqi.mm"
include "cvv.mm"
include "fvex.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem minveclem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vw: setvar w
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cK: class K
  let cT: class T
  let cL: class L
  assume minvec.x: |- X = ( Base ` U )
  assume minvec.m: |- .- = ( -g ` U )
  assume minvec.n: |- N = ( norm ` U )
  assume minvec.u: |- ( ph -> U e. CPreHil )
  assume minvec.y: |- ( ph -> Y e. ( LSubSp ` U ) )
  assume minvec.w: |- ( ph -> ( U |`s Y ) e. CMetSp )
  assume minvec.a: |- ( ph -> A e. X )
  assume minvec.j: |- J = ( TopOpen ` U )
  assume minvec.r: |- R = ran ( y e. Y |-> ( N ` ( A .- y ) ) )
  assume minvec.s: |- S = inf ( R , RR , < )
  assume minvec.d: |- D = ( ( dist ` U ) |` ( X X. X ) )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint S y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint .- j
  disjoint w x
  disjoint w y
  disjoint .- w
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j z
  disjoint A j
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint J r
  disjoint J w
  disjoint P x
  disjoint P y
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint N j
  disjoint N w
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint R w
  disjoint U w
  disjoint X r
  disjoint X w
  disjoint Y j
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ( ph /\ x e. Y ) -> ( ( ( A D x ) ^ 2 ) <_ ( ( S ^ 2 ) + 0 ) <-> A. y e. Y ( N ` ( A .- x ) ) <_ ( N ` ( A .- y ) ) ) )

  proof
    wph
    vx
    cv
    #
    cY
    wcel
    #
    wa
    #
    cA
    @0
    cD
    co
    #
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    cc0
    caddc
    co
    #
    cle
    wbr
    #
    cA
    @0
    c.mi
    co
    #
    cN
    cfv
    #
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    @9
    cA
    vy
    cv
    c.mi
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vy
    cY
    wral
    #
    @2
    @7
    @9
    c2
    cexp
    co
    #
    @5
    cle
    wbr
    @9
    cS
    cle
    wbr
    #
    @12
    @2
    @4
    @17
    @6
    @5
    cle
    @2
    @3
    @9
    c2
    cexp
    @2
    @3
    cA
    @0
    cU
    cds
    cfv
    #
    co
    #
    @9
    @2
    @3
    cA
    @0
    @19
    cX
    cX
    cxp
    cres
    #
    co
    @20
    cD
    @21
    cA
    @0
    minvec.d
    oveqi
    @2
    cA
    @0
    @19
    cX
    wph
    cA
    cX
    wcel
    #
    @1
    minvec.a
    adantr
    #
    wph
    cY
    cX
    @0
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    cY
    cX
    wss
    minvec.y
    @24
    cY
    cX
    cU
    minvec.x
    @24
    eqid
    lssss
    syl
    sselda
    #
    ovresd
    syl5eq
    @2
    cU
    cngp
    wcel
    #
    @22
    @0
    cX
    wcel
    #
    @20
    @9
    wceq
    wph
    @26
    @1
    wph
    cU
    ccph
    wcel
    #
    @26
    minvec.u
    cU
    cphngp
    syl
    adantr
    #
    @23
    @25
    cA
    @0
    @19
    cU
    c.mi
    cN
    cX
    minvec.n
    minvec.x
    minvec.m
    @19
    eqid
    ngpds
    syl3anc
    eqtrd
    oveq1d
    @2
    @5
    @2
    @5
    @2
    cS
    @2
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minvec.s
    @2
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    @0
    @10
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vx
    cr
    wrex
    #
    @30
    cr
    wcel
    @2
    @31
    @32
    cc0
    @10
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    @31
    @32
    @37
    w3a
    @1
    wph
    vy
    vw
    cA
    cR
    cU
    cJ
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minveclem1
    adantr
    #
    simp1d
    #
    @2
    @31
    @32
    @37
    @38
    simp2d
    #
    @2
    cc0
    cr
    wcel
    #
    @37
    @35
    @2
    0red
    #
    @2
    @31
    @32
    @37
    @38
    simp3d
    #
    @34
    @37
    vx
    cc0
    cr
    @0
    cc0
    wceq
    @33
    @36
    vw
    cR
    @0
    cc0
    @10
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    #
    vx
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
    #
    resqcld
    recnd
    addid1d
    breq12d
    @2
    @9
    cS
    @2
    @26
    @8
    cX
    wcel
    #
    @9
    cr
    wcel
    #
    @29
    @2
    cU
    clmod
    wcel
    #
    @22
    @27
    @46
    wph
    @48
    @1
    wph
    @28
    @48
    minvec.u
    cU
    cphlmod
    syl
    adantr
    @23
    @25
    c.mi
    cX
    cU
    cA
    @0
    minvec.x
    minvec.m
    lmodvsubcl
    syl3anc
    #
    @8
    cU
    cN
    cX
    minvec.x
    minvec.n
    nmcl
    syl2anc
    #
    @45
    @2
    @26
    @46
    cc0
    @9
    cle
    wbr
    @29
    @49
    @8
    cU
    cN
    cX
    minvec.x
    minvec.n
    nmge0
    syl2anc
    @2
    cc0
    @30
    cS
    cle
    @2
    cc0
    @30
    cle
    wbr
    #
    @37
    @43
    @2
    @31
    @32
    @35
    @41
    @51
    @37
    wb
    @39
    @40
    @44
    @42
    vx
    vw
    vw
    cR
    cc0
    infregelb
    syl31anc
    mpbird
    minvec.s
    syl6breqr
    le2sqd
    @18
    @9
    @30
    cle
    wbr
    #
    @2
    @12
    cS
    @30
    @9
    cle
    minvec.s
    breq2i
    @2
    @31
    @32
    @35
    @47
    @52
    @12
    wb
    @39
    @40
    @44
    @50
    vx
    vw
    vw
    cR
    @9
    infregelb
    syl31anc
    syl5bb
    3bitr2d
    @12
    @11
    vw
    vy
    cY
    @14
    cmpt
    #
    crn
    #
    wral
    #
    @16
    @11
    vw
    cR
    @54
    minvec.r
    raleqi
    @14
    cvv
    wcel
    #
    vy
    cY
    wral
    @55
    @16
    wb
    @56
    vy
    cY
    @13
    cN
    fvex
    rgenw
    @11
    @15
    vy
    vw
    cY
    @14
    @53
    cvv
    @53
    eqid
    @10
    @14
    @9
    cle
    breq2
    ralrnmpt
    ax-mp
    bitri
    syl6bb
end
