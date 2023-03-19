include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "wfal.mm"
include "fal.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "cmin.mm"
include "cif.mm"
include "clt.mm"
include "cc.mm"
include "reccld.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "simpr.mm"
include "1re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "max1.mm"
include "sylancr.mm"
include "rpgecld.mm"
include "rpreccld.mm"
include "crli.mm"
include "rlimi.mm"
include "wss.mm"
include "wb.mm"
include "cdm.mm"
include "wceq.mm"
include "dmmptg.mm"
include "syl.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "rexanre.mm"
include "cxr.mm"
include "csup.mm"
include "cpnf.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrunb1.mm"
include "mpbird.mm"
include "r19.29.mm"
include "r19.29r.mm"
include "wn.mm"
include "adantlr.mm"
include "wne.mm"
include "absrpcld.mm"
include "ad2antrr.mm"
include "0le1.mm"
include "rpred.mm"
include "max2.mm"
include "letrd.mm"
include "lediv2ad.mm"
include "rprecred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "1cnd.mm"
include "absdivd.mm"
include "absidd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "breq1d.mm"
include "mtbird.mm"
include "pm2.21d.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "imim2d.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "rexlimdvw.mm"
include "mpand.mm"
include "sylbird.mm"
include "mtoi.mm"
include "nrexdv.mm"
include "elo1mpt.mm"
include "rexcom.mm"
include "syl6bb.mm"

theorem rlimno1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vy: setvar y
  assume rlimno1.1: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimno1.2: |- ( ph -> ( x e. A |-> ( 1 / B ) ) ~~>r 0 )
  assume rlimno1.3: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume rlimno1.4: |- ( ( ph /\ x e. A ) -> B =/= 0 )

  disjoint A x
  disjoint ph x
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint x y
  disjoint A y
  disjoint B c
  disjoint B y
  disjoint c ph
  disjoint ph y
  assert |- ( ph -> -. ( x e. A |-> B ) e. O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    co1
    wcel
    #
    vc
    cv
    vx
    cv
    #
    cle
    wbr
    #
    cB
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    wi
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    wph
    @7
    vy
    cr
    wph
    @4
    cr
    wcel
    #
    wa
    #
    @7
    wfal
    fal
    @10
    @2
    c1
    cB
    cdiv
    co
    #
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    c1
    @4
    cle
    wbr
    #
    @4
    c1
    cif
    #
    cdiv
    co
    #
    clt
    wbr
    #
    wi
    vx
    cA
    wral
    vc
    cr
    wrex
    #
    @7
    wfal
    @10
    vc
    vx
    cA
    @11
    cc0
    @16
    cc
    wph
    @11
    cc
    wcel
    #
    vx
    cA
    wral
    #
    @9
    wph
    @19
    vx
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    cB
    rlimno1.3
    rlimno1.4
    reccld
    ralrimiva
    #
    adantr
    @10
    @15
    @10
    @15
    c1
    @10
    @9
    c1
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    wph
    @9
    simpr
    #
    1re
    @14
    @4
    c1
    cr
    ifcl
    sylancl
    #
    c1
    crp
    wcel
    @10
    1rp
    a1i
    @10
    @23
    @9
    c1
    @15
    cle
    wbr
    1re
    @25
    c1
    @4
    max1
    sylancr
    rpgecld
    #
    rpreccld
    wph
    vx
    cA
    @11
    cmpt
    #
    cc0
    crli
    wbr
    #
    @9
    rlimno1.2
    adantr
    rlimi
    @10
    @18
    @7
    wa
    #
    @2
    @17
    @5
    wa
    #
    wi
    #
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    wfal
    @10
    cA
    cr
    wss
    #
    @34
    @30
    wb
    wph
    @35
    @9
    wph
    cA
    @28
    cdm
    #
    cr
    wph
    @20
    @36
    cA
    wceq
    @22
    vx
    cA
    @11
    cc
    dmmptg
    syl
    wph
    @29
    @36
    cr
    wss
    rlimno1.2
    cc0
    @28
    rlimss
    syl
    eqsstr3d
    #
    adantr
    @17
    @5
    cA
    vc
    vx
    rexanre
    syl
    @10
    @2
    vx
    cA
    wrex
    #
    vc
    cr
    wral
    #
    @34
    wfal
    wph
    @39
    @9
    wph
    @39
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    rlimno1.1
    wph
    cA
    cxr
    wss
    @39
    @40
    wb
    wph
    cA
    cr
    cxr
    @37
    ressxr
    syl6ss
    vc
    vx
    cA
    supxrunb1
    syl
    mpbird
    adantr
    @39
    @34
    wa
    @38
    @33
    wa
    #
    vc
    cr
    wrex
    @10
    wfal
    @38
    @33
    vc
    cr
    r19.29
    @10
    @41
    wfal
    vc
    cr
    @41
    @2
    @32
    wa
    #
    vx
    cA
    wrex
    @10
    wfal
    @2
    @32
    vx
    cA
    r19.29r
    @10
    @42
    wfal
    vx
    cA
    @10
    @21
    wa
    #
    @2
    @32
    wfal
    @43
    @32
    @2
    wfal
    @43
    @31
    wfal
    @2
    @43
    @5
    @17
    wfal
    @43
    @5
    @17
    wfal
    @43
    @5
    wa
    #
    @17
    wfal
    @44
    @17
    c1
    @3
    cdiv
    co
    #
    @16
    clt
    wbr
    #
    @44
    @16
    @45
    cle
    wbr
    @46
    wn
    @44
    @3
    @15
    c1
    @43
    @3
    crp
    wcel
    @5
    @43
    cB
    wph
    @21
    cB
    cc
    wcel
    #
    @9
    rlimno1.3
    adantlr
    #
    wph
    @21
    cB
    cc0
    wne
    #
    @9
    rlimno1.4
    adantlr
    #
    absrpcld
    adantr
    #
    @10
    @15
    crp
    wcel
    @21
    @5
    @27
    ad2antrr
    #
    @23
    @44
    1re
    a1i
    #
    cc0
    c1
    cle
    wbr
    @44
    0le1
    a1i
    #
    @44
    @3
    @4
    @15
    @44
    @3
    @51
    rpred
    @10
    @9
    @21
    @5
    @25
    ad2antrr
    #
    @10
    @24
    @21
    @5
    @26
    ad2antrr
    @43
    @5
    simpr
    @44
    @23
    @9
    @4
    @15
    cle
    wbr
    1re
    @55
    c1
    @4
    max2
    sylancr
    letrd
    lediv2ad
    @44
    @16
    @45
    @44
    @15
    @52
    rprecred
    @44
    @3
    @51
    rprecred
    lenltd
    mpbid
    @44
    @13
    @45
    @16
    clt
    @44
    @13
    @11
    cabs
    cfv
    c1
    cabs
    cfv
    #
    @3
    cdiv
    co
    @45
    @44
    @12
    @11
    cabs
    @44
    @11
    @44
    cB
    @43
    @47
    @5
    @48
    adantr
    #
    @43
    @49
    @5
    @50
    adantr
    #
    reccld
    subid1d
    fveq2d
    @44
    c1
    cB
    @44
    1cnd
    @57
    @58
    absdivd
    @44
    @56
    c1
    @3
    cdiv
    @44
    c1
    @53
    @54
    absidd
    oveq1d
    3eqtrd
    breq1d
    mtbird
    pm2.21d
    expimpd
    ancomsd
    imim2d
    com23
    impd
    rexlimdva
    syl5
    rexlimdvw
    syl5
    mpand
    sylbird
    mpand
    mtoi
    nrexdv
    wph
    @0
    @6
    vy
    cr
    wrex
    vc
    cr
    wrex
    @8
    wph
    vx
    vc
    cA
    cB
    vy
    @37
    rlimno1.3
    elo1mpt
    @6
    vc
    vy
    cr
    cr
    rexcom
    syl6bb
    mtbird
end
