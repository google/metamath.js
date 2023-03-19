include "crli.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "csb.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wcel.mm"
include "wne.mm"
include "cr.mm"
include "cioo.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "rexrd.mm"
include "renepnfd.mm"
include "icopnfsup.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cc.mm"
include "wf.mm"
include "dvfsumrlimf.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "wss.mm"
include "syl6eleq.mm"
include "wb.mm"
include "elioopnf.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "cle.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss1.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "subcld.mm"
include "cmpt.mm"
include "pnfxr.mm"
include "icossre.mm"
include "sylancl.mm"
include "cdm.mm"
include "rlimf.mm"
include "adantl.mm"
include "cfl.mm"
include "cfz.mm"
include "csu.mm"
include "ovex.mm"
include "dmmpti.mm"
include "feq2i.mm"
include "sylib.mm"
include "rlimconst.mm"
include "feqmptd.mm"
include "simpr.mm"
include "eqbrtrrd.mm"
include "rlimres2.mm"
include "rlimsub.mm"
include "rlimabs.mm"
include "wral.mm"
include "a1i.mm"
include "dvmptrecl.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "abscld.mm"
include "abssubd.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "adantlr.mm"
include "cdv.mm"
include "w3a.mm"
include "3simpa.mm"
include "syl3an3.mm"
include "3adant1r.mm"
include "cc0.mm"
include "dvfsumrlimge0.mm"
include "3adantr3.mm"
include "elicopnf.mm"
include "simplbda.mm"
include "simprbda.mm"
include "pnfge.mm"
include "dvfsumlem4.mm"
include "eqbrtrd.mm"
include "rlimle.mm"

theorem dvfsumrlim2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cL: class L
  let cM: class M
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let ve: setvar e
  let vm: setvar m
  let cE: class E
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cY: class Y
  let cU: class U
  assume dvfsum.s: |- S = ( T (,) +oo )
  assume dvfsum.z: |- Z = ( ZZ>= ` M )
  assume dvfsum.m: |- ( ph -> M e. ZZ )
  assume dvfsum.d: |- ( ph -> D e. RR )
  assume dvfsum.md: |- ( ph -> M <_ ( D + 1 ) )
  assume dvfsum.t: |- ( ph -> T e. RR )
  assume dvfsum.a: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume dvfsum.b1: |- ( ( ph /\ x e. S ) -> B e. V )
  assume dvfsum.b2: |- ( ( ph /\ x e. Z ) -> B e. RR )
  assume dvfsum.b3: |- ( ph -> ( RR _D ( x e. S |-> A ) ) = ( x e. S |-> B ) )
  assume dvfsum.c: |- ( x = k -> B = C )
  assume dvfsumrlim.l: |- ( ( ph /\ ( x e. S /\ k e. S ) /\ ( D <_ x /\ x <_ k ) ) -> C <_ B )
  assume dvfsumrlim.g: |- G = ( x e. S |-> ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) )
  assume dvfsumrlim.k: |- ( ph -> ( x e. S |-> B ) ~~>r 0 )
  assume dvfsumrlim2.1: |- ( ph -> X e. S )
  assume dvfsumrlim2.2: |- ( ph -> D <_ X )

  disjoint B k
  disjoint C x
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint S x
  disjoint M k
  disjoint M x
  disjoint T x
  disjoint Z x
  disjoint X k
  disjoint X x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint c e
  disjoint c k
  disjoint c m
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint e k
  disjoint e m
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint x z
  disjoint C z
  disjoint c x
  disjoint D c
  disjoint x y
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint G c
  disjoint G e
  disjoint G y
  disjoint G z
  disjoint H m
  disjoint H y
  disjoint H z
  disjoint c ph
  disjoint e x
  disjoint e ph
  disjoint m x
  disjoint m ph
  disjoint ph y
  disjoint S c
  disjoint S e
  disjoint S m
  disjoint S y
  disjoint S z
  disjoint L y
  disjoint M z
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint T c
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint T u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint T v
  disjoint w x
  disjoint w z
  disjoint T w
  disjoint T z
  disjoint Y k
  disjoint Y m
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint U k
  disjoint U x
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint X m
  disjoint u y
  disjoint X u
  disjoint v y
  disjoint X v
  disjoint w y
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( ph /\ G ~~>r L ) -> ( abs ` ( ( G ` X ) - L ) ) <_ [_ X / x ]_ B )

  proof
    wph
    cG
    cL
    crli
    wbr
    #
    wa
    #
    vy
    cX
    cpnf
    cico
    co
    #
    cX
    cG
    cfv
    #
    vy
    cv
    #
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cX
    cB
    csb
    #
    @3
    cL
    cmin
    co
    #
    cabs
    cfv
    @8
    wph
    @2
    cxr
    clt
    csup
    cpnf
    wceq
    #
    @0
    wph
    cX
    cxr
    wcel
    cX
    cpnf
    wne
    @10
    wph
    cX
    wph
    cS
    cr
    cX
    cS
    cT
    cpnf
    cioo
    co
    #
    cr
    dvfsum.s
    cT
    cpnf
    ioossre
    eqsstri
    #
    dvfsumrlim2.1
    sseldi
    #
    rexrd
    wph
    cX
    @13
    renepnfd
    cX
    icopnfsup
    syl2anc
    adantr
    @1
    @2
    @6
    @9
    vy
    cc
    @1
    @4
    @2
    wcel
    #
    wa
    #
    @3
    @5
    @15
    @3
    @15
    cS
    cr
    cX
    cG
    wph
    cS
    cr
    cG
    wf
    @0
    @14
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cM
    cV
    cZ
    dvfsum.s
    dvfsum.z
    dvfsum.m
    dvfsum.d
    dvfsum.md
    dvfsum.t
    dvfsum.a
    dvfsum.b1
    dvfsum.b2
    dvfsum.b3
    dvfsum.c
    dvfsumrlim.g
    dvfsumrlimf
    ad2antrr
    #
    wph
    cX
    cS
    wcel
    #
    @0
    @14
    dvfsumrlim2.1
    ad2antrr
    ffvelrnd
    recnd
    #
    @15
    @5
    @15
    cS
    cr
    @4
    cG
    @16
    @1
    @2
    cS
    @4
    wph
    @2
    cS
    wss
    @0
    wph
    @2
    @11
    cS
    wph
    cT
    cxr
    wcel
    #
    cT
    cX
    clt
    wbr
    #
    @2
    @11
    wss
    wph
    cT
    dvfsum.t
    rexrd
    #
    wph
    cX
    cr
    wcel
    #
    @20
    wph
    cX
    @11
    wcel
    #
    @22
    @20
    wa
    #
    wph
    cX
    cS
    @11
    dvfsumrlim2.1
    dvfsum.s
    syl6eleq
    wph
    @19
    @23
    @24
    wb
    @21
    cT
    cX
    elioopnf
    syl
    mpbid
    simprd
    vu
    vv
    vw
    vz
    cT
    cX
    cpnf
    cico
    clt
    clt
    cle
    cioo
    clt
    vu
    vv
    vw
    df-ioo
    vu
    vv
    vw
    df-ico
    cT
    cX
    vz
    cv
    xrltletr
    ixxss1
    syl2anc
    dvfsum.s
    syl6sseqr
    #
    adantr
    #
    sselda
    ffvelrnd
    recnd
    #
    subcld
    #
    @1
    vy
    @2
    @3
    @5
    @3
    cL
    cc
    @18
    @27
    @1
    @2
    cr
    wss
    #
    @3
    cc
    wcel
    vy
    @2
    @3
    cmpt
    @3
    crli
    wbr
    wph
    @29
    @0
    wph
    @22
    cpnf
    cxr
    wcel
    #
    @29
    @13
    pnfxr
    cX
    cpnf
    icossre
    sylancl
    #
    adantr
    @1
    cS
    cc
    cX
    cG
    @1
    cG
    cdm
    #
    cc
    cG
    wf
    #
    cS
    cc
    cG
    wf
    @0
    @33
    wph
    cL
    cG
    rlimf
    adantl
    @32
    cS
    cc
    cG
    vx
    cS
    cM
    vx
    cv
    #
    cfl
    cfv
    cfz
    co
    cC
    vk
    csu
    #
    cA
    cmin
    co
    cG
    @35
    cA
    cmin
    ovex
    dvfsumrlim.g
    dmmpti
    feq2i
    sylib
    #
    wph
    @17
    @0
    dvfsumrlim2.1
    adantr
    ffvelrnd
    vy
    @2
    @3
    rlimconst
    syl2anc
    @1
    vy
    @2
    cS
    @5
    cL
    @26
    @1
    cG
    vy
    cS
    @5
    cmpt
    cL
    crli
    @1
    vy
    cS
    cc
    cG
    @36
    feqmptd
    wph
    @0
    simpr
    eqbrtrrd
    rlimres2
    rlimsub
    rlimabs
    wph
    vy
    @2
    @8
    cmpt
    @8
    crli
    wbr
    #
    @0
    wph
    @29
    @8
    cc
    wcel
    @37
    @31
    wph
    @8
    wph
    @17
    cB
    cr
    wcel
    #
    vx
    cS
    wral
    @8
    cr
    wcel
    #
    dvfsumrlim2.1
    wph
    @38
    vx
    cS
    wph
    vx
    cA
    cB
    cS
    cV
    cS
    cr
    wss
    wph
    @12
    a1i
    dvfsum.a
    dvfsum.b1
    dvfsum.b3
    dvmptrecl
    ralrimiva
    @38
    @39
    vx
    cX
    cS
    vx
    @8
    cr
    vx
    cX
    cB
    nfcsb1v
    nfel1
    @34
    cX
    wceq
    cB
    @8
    cr
    vx
    cX
    cB
    csbeq1a
    eleq1d
    rspc
    sylc
    #
    recnd
    vy
    @2
    @8
    rlimconst
    syl2anc
    adantr
    @15
    @6
    @28
    abscld
    wph
    @39
    @0
    @14
    @40
    ad2antrr
    @15
    @7
    @5
    @3
    cmin
    co
    cabs
    cfv
    #
    @8
    cle
    @15
    @3
    @5
    @18
    @27
    abssubd
    wph
    @14
    @41
    @8
    cle
    wbr
    @0
    wph
    @14
    wa
    #
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cpnf
    vk
    cG
    cM
    cV
    cX
    @4
    cZ
    dvfsum.s
    dvfsum.z
    wph
    cM
    cz
    wcel
    @14
    dvfsum.m
    adantr
    wph
    cD
    cr
    wcel
    @14
    dvfsum.d
    adantr
    wph
    cM
    cD
    c1
    caddc
    co
    cle
    wbr
    @14
    dvfsum.md
    adantr
    wph
    cT
    cr
    wcel
    @14
    dvfsum.t
    adantr
    wph
    @34
    cS
    wcel
    #
    cA
    cr
    wcel
    @14
    dvfsum.a
    adantlr
    wph
    @43
    cB
    cV
    wcel
    @14
    dvfsum.b1
    adantlr
    wph
    @34
    cZ
    wcel
    @38
    @14
    dvfsum.b2
    adantlr
    wph
    cr
    vx
    cS
    cA
    cmpt
    cdv
    co
    vx
    cS
    cB
    cmpt
    wceq
    @14
    dvfsum.b3
    adantr
    dvfsum.c
    @30
    @42
    pnfxr
    a1i
    wph
    @43
    vk
    cv
    #
    cS
    wcel
    wa
    #
    cD
    @34
    cle
    wbr
    #
    @34
    @44
    cle
    wbr
    #
    @44
    cpnf
    cle
    wbr
    #
    w3a
    #
    cC
    cB
    cle
    wbr
    #
    @14
    @49
    wph
    @45
    @46
    @47
    wa
    @50
    @46
    @47
    @48
    3simpa
    dvfsumrlim.l
    syl3an3
    3adant1r
    dvfsumrlim.g
    wph
    @43
    @46
    @34
    cpnf
    cle
    wbr
    #
    w3a
    cc0
    cB
    cle
    wbr
    #
    @14
    wph
    @43
    @46
    @52
    @51
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cM
    cV
    cZ
    dvfsum.s
    dvfsum.z
    dvfsum.m
    dvfsum.d
    dvfsum.md
    dvfsum.t
    dvfsum.a
    dvfsum.b1
    dvfsum.b2
    dvfsum.b3
    dvfsum.c
    dvfsumrlim.l
    dvfsumrlim.g
    dvfsumrlim.k
    dvfsumrlimge0
    3adantr3
    adantlr
    wph
    @17
    @14
    dvfsumrlim2.1
    adantr
    wph
    @2
    cS
    @4
    @25
    sselda
    wph
    cD
    cX
    cle
    wbr
    @14
    dvfsumrlim2.2
    adantr
    wph
    @14
    @4
    cr
    wcel
    #
    cX
    @4
    cle
    wbr
    #
    wph
    @22
    @14
    @53
    @54
    wa
    wb
    @13
    cX
    @4
    elicopnf
    syl
    #
    simplbda
    @42
    @4
    cxr
    wcel
    @4
    cpnf
    cle
    wbr
    @42
    @4
    wph
    @14
    @53
    @54
    @55
    simprbda
    rexrd
    @4
    pnfge
    syl
    dvfsumlem4
    adantlr
    eqbrtrd
    rlimle
end
