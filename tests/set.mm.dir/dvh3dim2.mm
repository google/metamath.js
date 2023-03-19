include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "dvh3dim.mm"
include "adantr.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "ad2antrr.mm"
include "lspprcl.mm"
include "lspprid1.mm"
include "simplr.mm"
include "lspprss.mm"
include "ssneld.mm"
include "ancrd.mm"
include "reximdva.mm"
include "mpd.mm"
include "w3a.mm"
include "cplusg.mm"
include "co.mm"
include "simpl1l.mm"
include "syl.mm"
include "simpl2.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lspprid2.mm"
include "simpl3.mm"
include "lssvancl2.mm"
include "simpr.mm"
include "simpl1r.mm"
include "lssvancl1.mm"
include "wceq.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "weq.mm"
include "pm2.61dan.mm"
include "rexlimdv3a.mm"

theorem dvh3dim2
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let c.0: class .0.
  let vw: setvar w
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )
  assume dvh3dim.y: |- ( ph -> Y e. V )
  assume dvh3dim2.z: |- ( ph -> Z e. V )

  disjoint N z
  disjoint U z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint Z z
  disjoint ph z
  disjoint K p
  disjoint p z
  disjoint N p
  disjoint .0. p
  disjoint .0. z
  disjoint U p
  disjoint V p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  disjoint p ph
  disjoint N w
  disjoint U w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint Z w
  disjoint ph w
  disjoint w z
  assert |- ( ph -> E. z e. V ( -. z e. ( N ` { X , Y } ) /\ -. z e. ( N ` { X , Z } ) ) )

  proof
    wph
    cY
    cX
    cZ
    cpr
    cN
    cfv
    #
    wcel
    #
    vz
    cv
    #
    cX
    cY
    cpr
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @2
    @0
    wcel
    #
    wn
    #
    wa
    #
    vz
    cV
    wrex
    #
    wph
    @1
    wa
    #
    @7
    vz
    cV
    wrex
    #
    @9
    wph
    @11
    @1
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cZ
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.x
    dvh3dim2.z
    dvh3dim
    adantr
    @10
    @7
    @8
    vz
    cV
    @10
    @2
    cV
    wcel
    #
    wa
    #
    @7
    @5
    @13
    @3
    @0
    @2
    @13
    cU
    clss
    cfv
    #
    @0
    cN
    cU
    cX
    cY
    @14
    eqid
    #
    dvh3dim.n
    wph
    cU
    clmod
    wcel
    #
    @1
    @12
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlmod
    #
    ad2antrr
    wph
    @0
    @14
    wcel
    #
    @1
    @12
    wph
    @14
    cN
    cV
    cU
    cX
    cZ
    dvh3dim.v
    @15
    dvh3dim.n
    @17
    dvh3dim.x
    dvh3dim2.z
    lspprcl
    #
    ad2antrr
    wph
    cX
    @0
    wcel
    @1
    @12
    wph
    cN
    cV
    cU
    cX
    cZ
    dvh3dim.v
    dvh3dim.n
    @17
    dvh3dim.x
    dvh3dim2.z
    lspprid1
    ad2antrr
    wph
    @1
    @12
    simplr
    lspprss
    ssneld
    ancrd
    reximdva
    mpd
    wph
    @1
    wn
    #
    wa
    #
    vw
    cv
    #
    @3
    wcel
    #
    wn
    #
    vw
    cV
    wrex
    #
    @9
    wph
    @25
    @20
    wph
    vw
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.x
    dvh3dim.y
    dvh3dim
    adantr
    @21
    @24
    @9
    vw
    cV
    @21
    @22
    cV
    wcel
    #
    @24
    w3a
    #
    @22
    @0
    wcel
    #
    @9
    @27
    @28
    wa
    #
    @22
    cY
    cU
    cplusg
    cfv
    #
    co
    #
    cV
    wcel
    #
    @31
    @3
    wcel
    #
    wn
    #
    @31
    @0
    wcel
    #
    wn
    #
    @9
    @29
    @16
    @26
    cY
    cV
    wcel
    #
    @32
    @29
    wph
    @16
    wph
    @20
    @26
    @24
    @28
    simpl1l
    #
    @17
    syl
    #
    @21
    @26
    @24
    @28
    simpl2
    #
    @29
    wph
    @37
    @38
    dvh3dim.y
    syl
    #
    @30
    cV
    cU
    @22
    cY
    dvh3dim.v
    @30
    eqid
    #
    lmodvacl
    syl3anc
    @29
    @30
    @14
    @3
    cV
    cU
    cY
    @22
    dvh3dim.v
    @42
    @15
    @39
    @29
    wph
    @3
    @14
    wcel
    @38
    wph
    @14
    cN
    cV
    cU
    cX
    cY
    dvh3dim.v
    @15
    dvh3dim.n
    @17
    dvh3dim.x
    dvh3dim.y
    lspprcl
    syl
    @29
    wph
    cY
    @3
    wcel
    @38
    wph
    cN
    cV
    cU
    cX
    cY
    dvh3dim.v
    dvh3dim.n
    @17
    dvh3dim.x
    dvh3dim.y
    lspprid2
    syl
    @40
    @21
    @26
    @24
    @28
    simpl3
    lssvancl2
    @29
    @30
    @14
    @0
    cV
    cU
    @22
    cY
    dvh3dim.v
    @42
    @15
    @39
    @29
    wph
    @18
    @38
    @19
    syl
    @27
    @28
    simpr
    @41
    wph
    @20
    @26
    @24
    @28
    simpl1r
    lssvancl1
    @8
    @34
    @36
    wa
    vz
    @31
    cV
    @2
    @31
    wceq
    #
    @5
    @34
    @7
    @36
    @43
    @4
    @33
    @2
    @31
    @3
    eleq1
    notbid
    @43
    @6
    @35
    @2
    @31
    @0
    eleq1
    notbid
    anbi12d
    rspcev
    syl12anc
    @27
    @28
    wn
    #
    wa
    @26
    @24
    @44
    @9
    @21
    @26
    @24
    @44
    simpl2
    @21
    @26
    @24
    @44
    simpl3
    @27
    @44
    simpr
    @8
    @24
    @44
    wa
    vz
    @22
    cV
    vz
    vw
    weq
    #
    @5
    @24
    @7
    @44
    @45
    @4
    @23
    @2
    @22
    @3
    eleq1
    notbid
    @45
    @6
    @28
    @2
    @22
    @0
    eleq1
    notbid
    anbi12d
    rspcev
    syl12anc
    pm2.61dan
    rexlimdv3a
    mpd
    pm2.61dan
end
