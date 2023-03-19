include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvsca.mm"
include "eqidd.mm"
include "wceq.mm"
include "a1i.mm"
include "clss.mm"
include "ciun.mm"
include "wral.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "wa.mm"
include "cpw.mm"
include "wn.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "sselda.mm"
include "elpwid.mm"
include "ssdifssd.mm"
include "lspssv.mm"
include "syl2an2r.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "lspcl.mm"
include "lssn0.mm"
include "r19.2z.mm"
include "syl2anc.mm"
include "iunn0.mm"
include "sylib.mm"
include "eqnetrd.mm"
include "co.mm"
include "eleq2i.mm"
include "eliun.mm"
include "weq.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "cbvrexv.mm"
include "3bitri.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "w3a.mm"
include "cun.mm"
include "crpss.mm"
include "wor.mm"
include "simp1l.mm"
include "simp2.mm"
include "sorpssun.mm"
include "elssuni.mm"
include "sspwuni.mm"
include "sstrd.mm"
include "simp1r.mm"
include "ssun1.mm"
include "ssdif.mm"
include "mp1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "sseldd.mm"
include "ssun2.mm"
include "simp3r.mm"
include "eqid.mm"
include "lsscl.mm"
include "syl13anc.mm"
include "eliuni.mm"
include "syl6eleqr.mm"
include "3expia.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "exp4b.mm"
include "3imp2.mm"
include "islssd.mm"
include "eldifi.mm"
include "adantl.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "eldif.mm"
include "lspssid.mm"
include "adantlr.mm"
include "sseld.mm"
include "syl5bir.mm"
include "mpan2d.mm"
include "reximdva.mm"
include "eluni2.mm"
include "3imtr4g.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl6sseqr.mm"
include "jca.mm"

theorem lbsextlem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vs: setvar s
  let vt: setvar t
  assume lbsext.v: |- V = ( Base ` W )
  assume lbsext.j: |- J = ( LBasis ` W )
  assume lbsext.n: |- N = ( LSpan ` W )
  assume lbsext.w: |- ( ph -> W e. LVec )
  assume lbsext.c: |- ( ph -> C C_ V )
  assume lbsext.x: |- ( ph -> A. x e. C -. x e. ( N ` ( C \ { x } ) ) )
  assume lbsext.s: |- S = { z e. ~P V | ( C C_ z /\ A. x e. z -. x e. ( N ` ( z \ { x } ) ) ) }
  assume lbsext.p: |- P = ( LSubSp ` W )
  assume lbsext.a: |- ( ph -> A C_ S )
  assume lbsext.z: |- ( ph -> A =/= (/) )
  assume lbsext.r: |- ( ph -> [C.] Or A )
  assume lbsext.t: |- T = U_ u e. A ( N ` ( u \ { x } ) )

  disjoint J x
  disjoint u x
  disjoint ph u
  disjoint ph x
  disjoint S u
  disjoint S x
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint u z
  disjoint N u
  disjoint N x
  disjoint N z
  disjoint V u
  disjoint V x
  disjoint V z
  disjoint W u
  disjoint W x
  disjoint A u
  disjoint A x
  disjoint A z
  disjoint m n
  disjoint m r
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m ph
  disjoint n r
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n ph
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint ph r
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph y
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint S s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint S w
  disjoint S y
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T v
  disjoint T w
  disjoint m z
  disjoint N m
  disjoint n z
  disjoint N n
  disjoint w z
  disjoint N w
  disjoint y z
  disjoint N y
  disjoint V w
  disjoint W m
  disjoint W n
  disjoint W r
  disjoint W v
  disjoint W w
  disjoint m s
  disjoint m t
  disjoint A m
  disjoint n s
  disjoint n t
  disjoint A n
  disjoint s z
  disjoint A s
  disjoint t z
  disjoint A t
  disjoint A y
  assert |- ( ph -> ( T e. P /\ ( U. A \ { x } ) C_ T ) )

  proof
    wph
    cT
    cP
    wcel
    cA
    cuni
    #
    vx
    cv
    #
    csn
    #
    cdif
    #
    cT
    wss
    wph
    vr
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cplusg
    cfv
    #
    cP
    cW
    cvsca
    cfv
    #
    cT
    @4
    cV
    cW
    vv
    vw
    wph
    @4
    eqidd
    wph
    @5
    eqidd
    cV
    cW
    cbs
    cfv
    wceq
    wph
    lbsext.v
    a1i
    wph
    @6
    eqidd
    wph
    @7
    eqidd
    cP
    cW
    clss
    cfv
    wceq
    wph
    lbsext.p
    a1i
    wph
    cT
    vu
    cA
    vu
    cv
    #
    @2
    cdif
    #
    cN
    cfv
    #
    ciun
    #
    cV
    lbsext.t
    wph
    @10
    cV
    wss
    #
    vu
    cA
    wral
    @11
    cV
    wss
    wph
    @12
    vu
    cA
    wph
    cW
    clmod
    wcel
    #
    @8
    cA
    wcel
    #
    @9
    cV
    wss
    #
    @12
    wph
    cW
    clvec
    wcel
    @13
    lbsext.w
    cW
    lveclmod
    syl
    #
    wph
    @14
    wa
    #
    @8
    cV
    @2
    @17
    @8
    cV
    wph
    cA
    cV
    cpw
    #
    @8
    wph
    cA
    cS
    @18
    lbsext.a
    cS
    cC
    vz
    cv
    #
    wss
    @1
    @19
    @2
    cdif
    cN
    cfv
    wcel
    wn
    vx
    @19
    wral
    wa
    #
    vz
    @18
    crab
    @18
    lbsext.s
    @20
    vz
    @18
    ssrab2
    eqsstri
    syl6ss
    #
    sselda
    elpwid
    ssdifssd
    #
    @9
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspssv
    syl2an2r
    ralrimiva
    vu
    cA
    @10
    cV
    iunss
    sylibr
    syl5eqss
    wph
    cT
    @11
    c0
    cT
    @11
    wceq
    wph
    lbsext.t
    a1i
    wph
    @10
    c0
    wne
    #
    vu
    cA
    wrex
    #
    @11
    c0
    wne
    wph
    cA
    c0
    wne
    @23
    vu
    cA
    wral
    @24
    lbsext.z
    wph
    @23
    vu
    cA
    @17
    @10
    cP
    wcel
    #
    @23
    wph
    @13
    @14
    @15
    @25
    @16
    @22
    cP
    @9
    cN
    cV
    cW
    lbsext.v
    lbsext.p
    lbsext.n
    lspcl
    syl2an2r
    cP
    @10
    cW
    lbsext.p
    lssn0
    syl
    ralrimiva
    @23
    vu
    cA
    r19.2z
    syl2anc
    vu
    cA
    @10
    iunn0
    sylib
    eqnetrd
    wph
    vr
    cv
    #
    @5
    wcel
    #
    vv
    cv
    #
    cT
    wcel
    #
    vw
    cv
    #
    cT
    wcel
    #
    @26
    @28
    @7
    co
    @30
    @6
    co
    #
    cT
    wcel
    #
    wph
    @27
    @29
    @31
    @33
    @29
    @31
    wa
    #
    @28
    vm
    cv
    #
    @2
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    @30
    vn
    cv
    #
    @2
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wa
    #
    vn
    cA
    wrex
    vm
    cA
    wrex
    #
    wph
    @27
    wa
    #
    @33
    @34
    @38
    vm
    cA
    wrex
    #
    @42
    vn
    cA
    wrex
    #
    wa
    @44
    @29
    @46
    @31
    @47
    @29
    @28
    @11
    wcel
    @28
    @10
    wcel
    #
    vu
    cA
    wrex
    @46
    cT
    @11
    @28
    lbsext.t
    eleq2i
    vu
    @28
    cA
    @10
    eliun
    @48
    @38
    vu
    vm
    cA
    vu
    vm
    weq
    #
    @10
    @37
    @28
    @49
    @9
    @36
    cN
    @8
    @35
    @2
    difeq1
    fveq2d
    eleq2d
    cbvrexv
    3bitri
    @31
    @30
    @11
    wcel
    @30
    @10
    wcel
    #
    vu
    cA
    wrex
    @47
    cT
    @11
    @30
    lbsext.t
    eleq2i
    vu
    @30
    cA
    @10
    eliun
    @50
    @42
    vu
    vn
    cA
    vu
    vn
    weq
    #
    @10
    @41
    @30
    @51
    @9
    @40
    cN
    @8
    @39
    @2
    difeq1
    fveq2d
    eleq2d
    cbvrexv
    3bitri
    anbi12i
    @38
    @42
    vm
    vn
    cA
    cA
    reeanv
    bitr4i
    @45
    @43
    @33
    vm
    vn
    cA
    cA
    @45
    @35
    cA
    wcel
    @39
    cA
    wcel
    wa
    #
    @43
    @33
    @45
    @52
    @43
    w3a
    #
    @32
    @11
    cT
    @53
    @35
    @39
    cun
    #
    cA
    wcel
    #
    @32
    @54
    @2
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    @32
    @11
    wcel
    @53
    cA
    crpss
    wor
    #
    @52
    @55
    @53
    wph
    @59
    wph
    @27
    @52
    @43
    simp1l
    #
    lbsext.r
    syl
    @45
    @52
    @43
    simp2
    cA
    @35
    @39
    sorpssun
    syl2anc
    #
    @53
    @57
    cP
    wcel
    #
    @27
    @28
    @57
    wcel
    @30
    @57
    wcel
    @58
    @53
    @13
    @56
    cV
    wss
    #
    @62
    @53
    wph
    @13
    @60
    @16
    syl
    #
    @53
    @54
    cV
    @2
    @53
    @54
    @0
    cV
    @53
    @55
    @54
    @0
    wss
    @61
    @54
    cA
    elssuni
    syl
    @53
    wph
    @0
    cV
    wss
    #
    @60
    wph
    cA
    @18
    wss
    @65
    @21
    cA
    cV
    sspwuni
    sylib
    syl
    sstrd
    ssdifssd
    #
    cP
    @56
    cN
    cV
    cW
    lbsext.v
    lbsext.p
    lbsext.n
    lspcl
    syl2anc
    wph
    @27
    @52
    @43
    simp1r
    @53
    @37
    @57
    @28
    @53
    @13
    @63
    @36
    @56
    wss
    #
    @37
    @57
    wss
    @64
    @66
    @35
    @54
    wss
    @67
    @53
    @35
    @39
    ssun1
    @35
    @54
    @2
    ssdif
    mp1i
    @36
    @56
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspss
    syl3anc
    @45
    @52
    @38
    @42
    simp3l
    sseldd
    @53
    @41
    @57
    @30
    @53
    @13
    @63
    @40
    @56
    wss
    #
    @41
    @57
    wss
    @64
    @66
    @39
    @54
    wss
    @68
    @53
    @39
    @35
    ssun2
    @39
    @54
    @2
    ssdif
    mp1i
    @40
    @56
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspss
    syl3anc
    @45
    @52
    @38
    @42
    simp3r
    sseldd
    @5
    @6
    cP
    @7
    @57
    @4
    cW
    @28
    @30
    @26
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    lbsext.p
    lsscl
    syl13anc
    vu
    @54
    @10
    @57
    cA
    @32
    @8
    @54
    wceq
    @9
    @56
    cN
    @8
    @54
    @2
    difeq1
    fveq2d
    eliuni
    syl2anc
    lbsext.t
    syl6eleqr
    3expia
    rexlimdvva
    syl5bi
    exp4b
    3imp2
    islssd
    wph
    @3
    @11
    cT
    wph
    vy
    @3
    @11
    wph
    vy
    cv
    #
    @3
    wcel
    #
    @69
    @11
    wcel
    #
    wph
    @70
    wa
    #
    @69
    @0
    wcel
    #
    @71
    @70
    @73
    wph
    @69
    @0
    @2
    eldifi
    adantl
    @72
    @69
    @8
    wcel
    #
    vu
    cA
    wrex
    @69
    @10
    wcel
    #
    vu
    cA
    wrex
    @73
    @71
    @72
    @74
    @75
    vu
    cA
    @72
    @14
    wa
    #
    @74
    @69
    @2
    wcel
    wn
    #
    @75
    @70
    @77
    wph
    @14
    @69
    @0
    @2
    eldifn
    ad2antlr
    @74
    @77
    wa
    @69
    @9
    wcel
    @76
    @75
    @69
    @8
    @2
    eldif
    @76
    @9
    @10
    @69
    wph
    @14
    @9
    @10
    wss
    #
    @70
    wph
    @13
    @14
    @15
    @78
    @16
    @22
    @9
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspssid
    syl2an2r
    adantlr
    sseld
    syl5bir
    mpan2d
    reximdva
    vu
    @69
    cA
    eluni2
    vu
    @69
    cA
    @10
    eliun
    3imtr4g
    mpd
    ex
    ssrdv
    lbsext.t
    syl6sseqr
    jca
end
