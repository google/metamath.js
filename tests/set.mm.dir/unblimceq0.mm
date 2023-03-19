include "cv.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "c0.mm"
include "wceq.mm"
include "cc.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "c1.mm"
include "1rp.mm"
include "a1i.mm"
include "wb.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "notbid.mm"
include "adantl.mm"
include "caddc.mm"
include "cle.mm"
include "w3a.mm"
include "simprr1.mm"
include "simprr2.mm"
include "jca.mm"
include "cr.mm"
include "1red.mm"
include "adantr.mm"
include "wf.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "abscld.mm"
include "simplr.mm"
include "resubcld.mm"
include "subcld.mm"
include "1cnd.mm"
include "recnd.mm"
include "pncand.mm"
include "eqcomd.mm"
include "simprr3.mm"
include "readdcld.mm"
include "lesub1d.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "abs2difd.mm"
include "letrd.mm"
include "lenltd.mm"
include "pm4.61.mm"
include "sylibr.mm"
include "3anbi2d.mm"
include "breq1.mm"
include "3anbi3d.mm"
include "unblimceq0lem.mm"
include "cc0.mm"
include "0lt1.mm"
include "absge0d.mm"
include "addgtge0d.mm"
include "elrpd.mm"
include "rspcdva.mm"
include "simpr.mm"
include "reximddv.mm"
include "rexnal.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "ralnex.mm"
include "rspcedvd.mm"
include "ex.mm"
include "imnan.mm"
include "ellimc3.mm"
include "mtbird.mm"
include "alrimiv.mm"
include "eq0.mm"

theorem unblimceq0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cF: class F
  let vb: setvar b
  let vd: setvar d
  let va: setvar a
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  let ve: setvar e
  assume unblimceq0.0: |- ( ph -> S C_ CC )
  assume unblimceq0.1: |- ( ph -> F : S --> CC )
  assume unblimceq0.2: |- ( ph -> A e. CC )
  assume unblimceq0.3: |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. S ( ( abs ` ( x - A ) ) < d /\ b <_ ( abs ` ( F ` x ) ) ) )

  disjoint A b
  disjoint A d
  disjoint A x
  disjoint b d
  disjoint b x
  disjoint d x
  disjoint F b
  disjoint F d
  disjoint F x
  disjoint S b
  disjoint S d
  disjoint S x
  disjoint b ph
  disjoint d ph
  disjoint ph x
  disjoint A a
  disjoint a b
  disjoint a d
  disjoint a x
  disjoint A c
  disjoint A y
  disjoint A z
  disjoint a c
  disjoint a y
  disjoint a z
  disjoint c d
  disjoint c y
  disjoint c z
  disjoint d y
  disjoint d z
  disjoint y z
  disjoint A e
  disjoint c e
  disjoint e y
  disjoint e z
  disjoint F a
  disjoint F c
  disjoint F y
  disjoint F z
  disjoint F e
  disjoint S a
  disjoint S c
  disjoint S z
  disjoint S e
  disjoint a ph
  disjoint c ph
  disjoint ph y
  disjoint ph z
  disjoint e ph
  disjoint x z
  assert |- ( ph -> ( F limCC A ) = (/) )

  proof
    wph
    vy
    cv
    #
    cF
    cA
    climc
    co
    #
    wcel
    #
    wn
    #
    vy
    wal
    @1
    c0
    wceq
    wph
    @3
    vy
    wph
    @2
    @0
    cc
    wcel
    #
    vz
    cv
    #
    cA
    wne
    #
    @5
    cA
    cmin
    co
    cabs
    cfv
    #
    vc
    cv
    #
    clt
    wbr
    #
    wa
    #
    @5
    cF
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cS
    wral
    #
    vc
    crp
    wrex
    #
    ve
    crp
    wral
    #
    wa
    #
    wph
    @4
    @19
    wn
    #
    wi
    @20
    wn
    wph
    @4
    @21
    wph
    @4
    wa
    #
    @18
    wn
    #
    ve
    crp
    wrex
    @21
    @22
    @23
    @10
    @13
    c1
    clt
    wbr
    #
    wi
    #
    vz
    cS
    wral
    #
    vc
    crp
    wrex
    #
    wn
    #
    ve
    c1
    crp
    c1
    crp
    wcel
    @22
    1rp
    a1i
    @14
    c1
    wceq
    #
    @23
    @28
    wb
    @22
    @29
    @18
    @27
    @29
    @17
    @26
    vc
    crp
    @29
    @16
    @25
    vz
    cS
    @29
    @15
    @24
    @10
    @14
    c1
    @13
    clt
    breq2
    imbi2d
    ralbidv
    rexbidv
    notbid
    adantl
    @22
    @26
    wn
    #
    vc
    crp
    wral
    @28
    @22
    @30
    vc
    crp
    @22
    @8
    crp
    wcel
    #
    wa
    #
    @25
    wn
    #
    vz
    cS
    wrex
    @30
    @32
    @6
    @9
    c1
    @0
    cabs
    cfv
    #
    caddc
    co
    #
    @11
    cabs
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    @33
    vz
    cS
    @32
    @5
    cS
    wcel
    #
    @38
    wa
    #
    wa
    #
    @10
    @24
    wn
    #
    wa
    @33
    @41
    @10
    @42
    @41
    @6
    @9
    @6
    @9
    @37
    @39
    @32
    simprr1
    @6
    @9
    @37
    @39
    @32
    simprr2
    jca
    @41
    c1
    @13
    cle
    wbr
    @42
    @41
    c1
    @36
    @34
    cmin
    co
    #
    @13
    @32
    c1
    cr
    wcel
    @40
    @32
    1red
    #
    adantr
    #
    @41
    @36
    @34
    @41
    @11
    @41
    cS
    cc
    @5
    cF
    @32
    cS
    cc
    cF
    wf
    #
    @40
    wph
    @46
    @4
    @31
    unblimceq0.1
    ad2antrr
    adantr
    @32
    @39
    @38
    simprl
    ffvelrnd
    #
    abscld
    #
    @32
    @34
    cr
    wcel
    @40
    @32
    @0
    wph
    @4
    @31
    simplr
    #
    abscld
    #
    adantr
    #
    resubcld
    @41
    @12
    @41
    @11
    @0
    @47
    @32
    @4
    @40
    @49
    adantr
    #
    subcld
    abscld
    #
    @41
    c1
    @35
    @34
    cmin
    co
    #
    @43
    cle
    @41
    @54
    c1
    @41
    c1
    @34
    @41
    1cnd
    @41
    @34
    @51
    recnd
    pncand
    eqcomd
    @41
    @37
    @54
    @43
    cle
    wbr
    @6
    @9
    @37
    @39
    @32
    simprr3
    @41
    @35
    @36
    @34
    @32
    @35
    cr
    wcel
    @40
    @32
    c1
    @34
    @44
    @50
    readdcld
    #
    adantr
    @48
    @51
    lesub1d
    mpbid
    eqbrtrd
    @41
    @11
    @0
    @47
    @52
    abs2difd
    letrd
    @41
    c1
    @13
    @45
    @53
    lenltd
    mpbid
    jca
    @10
    @24
    pm4.61
    sylibr
    @32
    @6
    @7
    vd
    cv
    #
    clt
    wbr
    #
    @37
    w3a
    #
    vz
    cS
    wrex
    #
    @38
    vz
    cS
    wrex
    vd
    crp
    @8
    @56
    @8
    wceq
    #
    @58
    @38
    vz
    cS
    @60
    @57
    @9
    @6
    @37
    @56
    @8
    @7
    clt
    breq2
    3anbi2d
    rexbidv
    @32
    @6
    @57
    va
    cv
    #
    @36
    cle
    wbr
    #
    w3a
    #
    vz
    cS
    wrex
    #
    vd
    crp
    wral
    #
    @59
    vd
    crp
    wral
    va
    crp
    @35
    @61
    @35
    wceq
    #
    @64
    @59
    vd
    crp
    @66
    @63
    @58
    vz
    cS
    @66
    @62
    @37
    @6
    @57
    @61
    @35
    @36
    cle
    breq1
    3anbi3d
    rexbidv
    ralbidv
    wph
    @65
    va
    crp
    wral
    @4
    @31
    wph
    vx
    vz
    cA
    cS
    cF
    vb
    va
    vd
    unblimceq0.0
    unblimceq0.1
    unblimceq0.2
    unblimceq0.3
    unblimceq0lem
    ad2antrr
    @32
    @35
    @55
    @32
    c1
    @34
    @44
    @50
    cc0
    c1
    clt
    wbr
    @32
    0lt1
    a1i
    @32
    @0
    @49
    absge0d
    addgtge0d
    elrpd
    rspcdva
    @22
    @31
    simpr
    rspcdva
    reximddv
    @25
    vz
    cS
    rexnal
    sylib
    ralrimiva
    @26
    vc
    crp
    ralnex
    sylib
    rspcedvd
    @18
    ve
    crp
    rexnal
    sylib
    ex
    @4
    @19
    imnan
    sylib
    wph
    ve
    vc
    vz
    cS
    cA
    @0
    cF
    unblimceq0.1
    unblimceq0.0
    unblimceq0.2
    ellimc3
    mtbird
    alrimiv
    vy
    @1
    eq0
    sylibr
end
