include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cr.mm"
include "cres.mm"
include "wf.mm"
include "cdm.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "uztrn2.mm"
include "adantll.mm"
include "wceq.mm"
include "cxr.mm"
include "fdmd.mm"
include "ad2antrr.mm"
include "eleqtrrd.mm"
include "adantlrr.mm"
include "simpll.mm"
include "rspa.mm"
include "w3a.mm"
include "ffvelrnda.mm"
include "3adant3.mm"
include "cmnf.mm"
include "wn.mm"
include "cle.mm"
include "simpr.mm"
include "simpl.mm"
include "eqeltrrd.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "adantl.mm"
include "eqbrtrrd.mm"
include "adantlrl.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "cli.mm"
include "cvv.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "eqidd.mm"
include "clim.mm"
include "mpbid.mm"
include "simpld.mm"
include "subcld.mm"
include "abscld.mm"
include "rpred.mm"
include "ltnled.mm"
include "pm2.65da.mm"
include "3adant2.mm"
include "neqned.mm"
include "cpnf.mm"
include "xrred.mm"
include "syl3anc.mm"
include "jca.mm"
include "ralrimia.mm"
include "wb.mm"
include "wfun.mm"
include "ffund.mm"
include "ffvresb.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "simprd.mm"
include "rspcdva.mm"
include "rexuz3.mm"
include "reximddv.mm"

theorem climxrrelem
  let wph: wff ph
  let cA: class A
  let cD: class D
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climxrrelem.m: |- ( ph -> M e. ZZ )
  assume climxrrelem.z: |- Z = ( ZZ>= ` M )
  assume climxrrelem.f: |- ( ph -> F : Z --> RR* )
  assume climxrrelem.c: |- ( ph -> F ~~> A )
  assume climxrrelem.d: |- ( ph -> D e. RR+ )
  assume climxrrelem.p: |- ( ( ph /\ +oo e. CC ) -> D <_ ( abs ` ( +oo - A ) ) )
  assume climxrrelem.n: |- ( ( ph /\ -oo e. CC ) -> D <_ ( abs ` ( -oo - A ) ) )

  disjoint A j
  disjoint D j
  disjoint F j
  disjoint M j
  disjoint Z j
  disjoint j ph
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F k
  disjoint F x
  disjoint Z k
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> E. j e. Z ( F |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> RR )

  proof
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @1
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cD
    clt
    wbr
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @8
    cr
    cF
    @8
    cres
    wf
    #
    vj
    cZ
    wph
    @7
    cZ
    wcel
    #
    @9
    wa
    #
    wa
    #
    @10
    @0
    cF
    cdm
    #
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    vk
    @8
    wral
    #
    @13
    @17
    vk
    @8
    wph
    @12
    vk
    wph
    vk
    nfv
    @11
    @9
    vk
    @11
    vk
    nfv
    @6
    vk
    @8
    nfra1
    nfan
    nfan
    @13
    @0
    @8
    wcel
    #
    wa
    #
    @15
    @16
    wph
    @11
    @19
    @15
    @9
    wph
    @11
    wa
    @19
    wa
    @0
    cZ
    @14
    @11
    @19
    @0
    cZ
    wcel
    #
    wph
    cM
    @0
    @7
    cZ
    climxrrelem.z
    uztrn2
    adantll
    #
    wph
    @14
    cZ
    wceq
    @11
    @19
    wph
    cZ
    cxr
    cF
    climxrrelem.f
    fdmd
    ad2antrr
    eleqtrrd
    adantlrr
    @20
    wph
    @21
    @6
    @16
    wph
    @12
    @19
    simpll
    wph
    @11
    @19
    @21
    @9
    @22
    adantlrr
    @12
    @19
    @6
    wph
    @9
    @19
    @6
    @11
    @6
    vk
    @8
    rspa
    adantll
    adantll
    wph
    @21
    @6
    w3a
    #
    @1
    wph
    @21
    @1
    cxr
    wcel
    @6
    wph
    cZ
    cxr
    @0
    cF
    climxrrelem.f
    ffvelrnda
    3adant3
    @23
    @1
    cmnf
    wph
    @6
    @1
    cmnf
    wceq
    #
    wn
    @21
    wph
    @6
    wa
    #
    @24
    cD
    cmnf
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wph
    @2
    @24
    @28
    @5
    wph
    @2
    wa
    #
    @24
    wa
    #
    wph
    cmnf
    cc
    wcel
    #
    @28
    wph
    @2
    @24
    simpll
    @2
    @24
    @31
    wph
    @2
    @24
    wa
    @1
    cmnf
    cc
    @2
    @24
    simpr
    @2
    @24
    simpl
    eqeltrrd
    adantll
    #
    climxrrelem.n
    syl2anc
    adantlrr
    @25
    @24
    wa
    #
    @27
    cD
    clt
    wbr
    #
    @28
    wn
    wph
    @5
    @24
    @34
    @2
    @5
    @24
    @34
    wph
    @5
    @24
    wa
    @4
    @27
    cD
    clt
    @24
    @4
    @27
    wceq
    @5
    @24
    @3
    @26
    cabs
    @1
    cmnf
    cA
    cmin
    oveq1
    fveq2d
    adantl
    @5
    @24
    simpl
    eqbrtrrd
    adantll
    adantlrl
    @33
    @27
    cD
    wph
    @2
    @24
    @27
    cr
    wcel
    @5
    @30
    @26
    @30
    cmnf
    cA
    @32
    wph
    cA
    cc
    wcel
    #
    @2
    @24
    wph
    @35
    @2
    @4
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @8
    wral
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wph
    cF
    cA
    cli
    wbr
    @35
    @40
    wa
    climxrrelem.c
    wph
    vx
    cA
    @1
    vj
    vk
    cF
    cvv
    wph
    cZ
    cxr
    cvv
    cF
    climxrrelem.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    climxrrelem.z
    fvexi
    a1i
    fexd
    wph
    @0
    cz
    wcel
    wa
    @1
    eqidd
    clim
    mpbid
    #
    simpld
    #
    ad2antrr
    subcld
    abscld
    adantlrr
    wph
    cD
    cr
    wcel
    #
    @6
    @24
    wph
    cD
    climxrrelem.d
    rpred
    #
    ad2antrr
    ltnled
    mpbid
    pm2.65da
    3adant2
    neqned
    @23
    @1
    cpnf
    wph
    @6
    @1
    cpnf
    wceq
    #
    wn
    @21
    @25
    @45
    cD
    cpnf
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wph
    @2
    @45
    @48
    @5
    @29
    @45
    wa
    #
    wph
    cpnf
    cc
    wcel
    #
    @48
    wph
    @2
    @45
    simpll
    @2
    @45
    @50
    wph
    @2
    @45
    wa
    @1
    cpnf
    cc
    @2
    @45
    simpr
    @2
    @45
    simpl
    eqeltrrd
    adantll
    #
    climxrrelem.p
    syl2anc
    adantlrr
    @25
    @45
    wa
    #
    @47
    cD
    clt
    wbr
    #
    @48
    wn
    wph
    @5
    @45
    @53
    @2
    @5
    @45
    @53
    wph
    @5
    @45
    wa
    @4
    @47
    cD
    clt
    @45
    @4
    @47
    wceq
    @5
    @45
    @3
    @46
    cabs
    @1
    cpnf
    cA
    cmin
    oveq1
    fveq2d
    adantl
    @5
    @45
    simpl
    eqbrtrrd
    adantll
    adantlrl
    @52
    @47
    cD
    wph
    @2
    @45
    @47
    cr
    wcel
    @5
    @49
    @46
    @49
    cpnf
    cA
    @51
    wph
    @35
    @2
    @45
    @42
    ad2antrr
    subcld
    abscld
    adantlrr
    wph
    @43
    @6
    @45
    @44
    ad2antrr
    ltnled
    mpbid
    pm2.65da
    3adant2
    neqned
    xrred
    syl3anc
    jca
    ralrimia
    wph
    @10
    @18
    wb
    #
    @12
    wph
    cF
    wfun
    @54
    wph
    cZ
    cxr
    cF
    climxrrelem.f
    ffund
    vk
    @8
    cr
    cF
    ffvresb
    syl
    adantr
    mpbird
    wph
    @9
    vj
    cZ
    wrex
    #
    @9
    vj
    cz
    wrex
    #
    wph
    @39
    @56
    vx
    crp
    cD
    @36
    cD
    wceq
    #
    @38
    @6
    vj
    vk
    cz
    @8
    @57
    @37
    @5
    @2
    @36
    cD
    @4
    clt
    breq2
    anbi2d
    rexralbidv
    wph
    @35
    @40
    @41
    simprd
    climxrrelem.d
    rspcdva
    wph
    cM
    cz
    wcel
    @55
    @56
    wb
    climxrrelem.m
    @6
    vj
    vk
    cM
    cZ
    climxrrelem.z
    rexuz3
    syl
    mpbird
    reximddv
end
