include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "clss.mm"
include "cvsca.mm"
include "crg.mm"
include "psrsca.mm"
include "eqidd.mm"
include "wceq.mm"
include "a1i.mm"
include "csubg.mm"
include "wcel.mm"
include "wss.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "mplsubglem.mm"
include "subgss.mm"
include "c0g.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "3syl.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "adantr.mm"
include "csupp.mm"
include "simprl.mm"
include "simprr.mm"
include "crab.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "mpbid.mm"
include "simpld.mm"
include "psrvscacl.mm"
include "cvv.mm"
include "wi.mm"
include "wal.mm"
include "ovex.mm"
include "wral.mm"
include "simprd.mm"
include "expr.mm"
include "alrimiv.mm"
include "ralrimiva.mm"
include "sseq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "psrelbas.mm"
include "cdif.mm"
include "cmulr.mm"
include "eldifi.mm"
include "adantl.mm"
include "psrvscaval.mm"
include "ssid.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "rabex2.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "syl2an2r.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "sseq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl3c.mm"
include "mpbir2and.mm"
include "3adantr3.mm"
include "simpr3.mm"
include "subgcl.mm"
include "syl3anc.mm"
include "islssd.mm"

theorem mpllsslem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume mplsubglem.s: |- S = ( I mPwSer R )
  assume mplsubglem.b: |- B = ( Base ` S )
  assume mplsubglem.z: |- .0. = ( 0g ` R )
  assume mplsubglem.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplsubglem.i: |- ( ph -> I e. W )
  assume mplsubglem.0: |- ( ph -> (/) e. A )
  assume mplsubglem.a: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x u. y ) e. A )
  assume mplsubglem.y: |- ( ( ph /\ ( x e. A /\ y C_ x ) ) -> y e. A )
  assume mplsubglem.u: |- ( ph -> U = { g e. B | ( g supp .0. ) e. A } )
  assume mpllsslem.r: |- ( ph -> R e. Ring )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint .0. f
  disjoint g x
  disjoint g y
  disjoint .0. g
  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint A f
  disjoint A g
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B g
  disjoint D g
  disjoint I f
  disjoint ph x
  disjoint ph y
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint f k
  disjoint f u
  disjoint g k
  disjoint g u
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint .0. k
  disjoint u x
  disjoint u y
  disjoint .0. u
  disjoint D u
  disjoint k v
  disjoint k w
  disjoint k ph
  disjoint u v
  disjoint u w
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint R k
  disjoint R v
  disjoint R w
  disjoint f v
  disjoint f w
  disjoint g v
  disjoint g w
  disjoint S k
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint U k
  disjoint U u
  disjoint U v
  disjoint U w
  assert |- ( ph -> U e. ( LSubSp ` S ) )

  proof
    wph
    vu
    cR
    cbs
    cfv
    #
    cS
    cplusg
    cfv
    #
    cS
    clss
    cfv
    #
    cS
    cvsca
    cfv
    #
    cU
    cR
    cB
    cS
    vv
    vw
    wph
    cR
    cS
    cI
    cW
    crg
    mplsubglem.s
    mplsubglem.i
    mpllsslem.r
    psrsca
    wph
    @0
    eqidd
    cB
    cS
    cbs
    cfv
    wceq
    wph
    mplsubglem.b
    a1i
    wph
    @1
    eqidd
    wph
    @3
    eqidd
    wph
    @2
    eqidd
    wph
    cU
    cS
    csubg
    cfv
    wcel
    #
    cU
    cB
    wss
    wph
    vx
    vy
    cA
    cB
    cD
    cR
    cS
    cU
    vf
    vg
    cI
    cW
    c.0
    mplsubglem.s
    mplsubglem.b
    mplsubglem.z
    mplsubglem.d
    mplsubglem.i
    mplsubglem.0
    mplsubglem.a
    mplsubglem.y
    mplsubglem.u
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    mpllsslem.r
    cR
    ringgrp
    syl
    mplsubglem
    #
    cB
    cU
    cS
    mplsubglem.b
    subgss
    syl
    wph
    @4
    cS
    c0g
    cfv
    #
    cU
    wcel
    cU
    c0
    wne
    @6
    cU
    cS
    @7
    @7
    eqid
    subg0cl
    cU
    @7
    ne0i
    3syl
    wph
    vu
    cv
    #
    @0
    wcel
    #
    vv
    cv
    #
    cU
    wcel
    #
    vw
    cv
    #
    cU
    wcel
    #
    w3a
    #
    wa
    @4
    @8
    @10
    @3
    co
    #
    cU
    wcel
    #
    @13
    @15
    @12
    @1
    co
    cU
    wcel
    wph
    @4
    @14
    @6
    adantr
    wph
    @9
    @11
    @16
    @13
    wph
    @9
    @11
    wa
    #
    wa
    #
    @16
    @15
    cB
    wcel
    #
    @15
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    @18
    cB
    cR
    cS
    @3
    @10
    cI
    @0
    @8
    mplsubglem.s
    @3
    eqid
    #
    @0
    eqid
    #
    mplsubglem.b
    wph
    @5
    @17
    mpllsslem.r
    adantr
    wph
    @9
    @11
    simprl
    #
    @18
    @10
    cB
    wcel
    #
    @10
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    @18
    @11
    @25
    @27
    wa
    #
    wph
    @9
    @11
    simprr
    @18
    @11
    @10
    vg
    cv
    #
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    vg
    cB
    crab
    #
    wcel
    @28
    @18
    cU
    @32
    @10
    wph
    cU
    @32
    wceq
    @17
    mplsubglem.u
    adantr
    #
    eleq2d
    @31
    @27
    vg
    @10
    cB
    @29
    @10
    wceq
    @30
    @26
    cA
    @29
    @10
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    mpbid
    #
    simpld
    #
    psrvscacl
    #
    @18
    @20
    cvv
    wcel
    #
    vy
    cv
    #
    @26
    wss
    #
    @38
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    @20
    @26
    wss
    #
    @21
    @37
    @18
    @15
    c.0
    csupp
    ovex
    a1i
    @18
    @27
    @38
    vx
    cv
    #
    wss
    #
    @40
    wi
    #
    vy
    wal
    #
    vx
    cA
    wral
    #
    @42
    @18
    @25
    @27
    @34
    simprd
    wph
    @48
    @17
    wph
    @47
    vx
    cA
    wph
    @44
    cA
    wcel
    #
    wa
    @46
    vy
    wph
    @49
    @45
    @40
    mplsubglem.y
    expr
    alrimiv
    ralrimiva
    adantr
    @47
    @42
    vx
    @26
    cA
    @44
    @26
    wceq
    #
    @46
    @41
    vy
    @50
    @45
    @39
    @40
    @44
    @26
    @38
    sseq2
    imbi1d
    albidv
    rspcv
    sylc
    @18
    cD
    @0
    vk
    @15
    @26
    c.0
    @18
    cB
    cD
    cR
    cS
    vf
    cI
    @0
    @15
    mplsubglem.s
    @23
    mplsubglem.d
    mplsubglem.b
    @36
    psrelbas
    @18
    vk
    cv
    #
    cD
    @26
    cdif
    wcel
    #
    wa
    #
    @51
    @15
    cfv
    @8
    @51
    @10
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    @8
    c.0
    @55
    co
    #
    c.0
    @53
    cB
    cD
    cR
    cS
    @3
    @55
    vf
    @10
    cI
    @0
    @8
    @51
    mplsubglem.s
    @22
    @23
    mplsubglem.b
    @55
    eqid
    #
    mplsubglem.d
    @18
    @9
    @52
    @24
    adantr
    @18
    @25
    @52
    @35
    adantr
    @52
    @51
    cD
    wcel
    @18
    @51
    cD
    @26
    eldifi
    adantl
    psrvscaval
    @53
    @54
    c.0
    @8
    @55
    @18
    cD
    @0
    cvv
    @10
    cvv
    @26
    @51
    c.0
    @18
    cB
    cD
    cR
    cS
    vf
    cI
    @0
    @10
    mplsubglem.s
    @23
    mplsubglem.d
    mplsubglem.b
    @35
    psrelbas
    @26
    @26
    wss
    @18
    @26
    ssid
    a1i
    cD
    cvv
    wcel
    @18
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    mplsubglem.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    c.0
    cvv
    wcel
    @18
    c.0
    cR
    c0g
    cfv
    cvv
    mplsubglem.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    suppssr
    oveq2d
    @18
    @56
    c.0
    wceq
    #
    @52
    wph
    @5
    @17
    @9
    @58
    mpllsslem.r
    @24
    @0
    cR
    @55
    @8
    c.0
    @23
    @57
    mplsubglem.z
    ringrz
    syl2an2r
    adantr
    3eqtrd
    suppss
    @41
    @43
    @21
    wi
    vy
    @20
    cvv
    @38
    @20
    wceq
    @39
    @43
    @40
    @21
    @38
    @20
    @26
    sseq1
    @38
    @20
    cA
    eleq1
    imbi12d
    spcgv
    syl3c
    @18
    @16
    @15
    @32
    wcel
    @19
    @21
    wa
    @18
    cU
    @32
    @15
    @33
    eleq2d
    @31
    @21
    vg
    @15
    cB
    @29
    @15
    wceq
    @30
    @20
    cA
    @29
    @15
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    mpbir2and
    3adantr3
    wph
    @9
    @11
    @13
    simpr3
    @1
    cU
    cS
    @15
    @12
    @1
    eqid
    subgcl
    syl3anc
    islssd
end
