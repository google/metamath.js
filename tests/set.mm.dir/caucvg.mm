include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crli.mm"
include "cli.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "cr.mm"
include "wss.mm"
include "cz.mm"
include "cuz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "cc.mm"
include "eqcomi.mm"
include "fmptd.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "eluzel2.mm"
include "eleq2s.mm"
include "a1d.mm"
include "rexlimiv.mm"
include "rexlimivw.mm"
include "syl.mm"
include "uzsup.mm"
include "cle.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "sseli.mm"
include "eluz.mm"
include "syl2an.mm"
include "biimprd.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt3i.mm"
include "oveqan12rd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imim12d.mm"
include "ex.mm"
include "com23.mm"
include "ralimdv2.mm"
include "reximia.mm"
include "ralimi.mm"
include "caucvgr.mm"
include "rlimdm.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "rlimclim.mm"
include "climmpt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "climrel.mm"
include "releldmi.mm"

theorem caucvg
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  assume caucvg.1: |- Z = ( ZZ>= ` M )
  assume caucvg.2: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume caucvg.3: |- ( ph -> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x )
  assume caucvg.4: |- ( ph -> F e. V )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint F i
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint M i
  disjoint M m
  disjoint M n
  disjoint i ph
  disjoint m ph
  disjoint n ph
  disjoint Z i
  disjoint Z m
  disjoint Z n
  assert |- ( ph -> F e. dom ~~> )

  proof
    wph
    cF
    vn
    cZ
    vn
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    crli
    cfv
    #
    cli
    wbr
    #
    cF
    cli
    cdm
    wcel
    wph
    @4
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    @3
    cli
    wbr
    #
    wph
    @7
    @3
    crli
    wbr
    @8
    wph
    @7
    @2
    @3
    crli
    vk
    vn
    cZ
    @6
    @1
    @5
    @0
    cF
    fveq2
    cbvmptv
    #
    wph
    @2
    crli
    cdm
    wcel
    @2
    @3
    crli
    wbr
    wph
    vx
    cZ
    vj
    vk
    @2
    cZ
    cr
    wss
    wph
    cZ
    cz
    cr
    cZ
    cM
    cuz
    cfv
    #
    cz
    caucvg.1
    cM
    uzssz
    eqsstri
    #
    zssre
    sstri
    a1i
    wph
    vk
    cZ
    @6
    cc
    @2
    caucvg.2
    @7
    @2
    @9
    eqcomi
    fmptd
    #
    wph
    cM
    cz
    wcel
    #
    cZ
    cxr
    clt
    csup
    cpnf
    wceq
    wph
    @6
    vj
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    @14
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wrex
    #
    @13
    wph
    crp
    c0
    wne
    @22
    vx
    crp
    wral
    #
    @23
    c1
    crp
    1rp
    ne0ii
    caucvg.3
    @22
    vx
    crp
    r19.2z
    sylancr
    @22
    @13
    vx
    crp
    @21
    @13
    vj
    cZ
    @14
    cZ
    wcel
    #
    @13
    @21
    @13
    @14
    @10
    cZ
    cM
    @14
    eluzel2
    caucvg.1
    eleq2s
    a1d
    rexlimiv
    rexlimivw
    syl
    #
    cM
    cZ
    caucvg.1
    uzsup
    syl
    #
    wph
    @24
    @14
    @5
    cle
    wbr
    #
    @5
    @2
    cfv
    #
    @14
    @2
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @18
    clt
    wbr
    #
    wi
    #
    vk
    cZ
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    caucvg.3
    @22
    @36
    vx
    crp
    @21
    @35
    vj
    cZ
    @25
    @19
    @34
    vk
    @20
    cZ
    @25
    @5
    cZ
    wcel
    #
    @5
    @20
    wcel
    #
    @19
    wi
    #
    @34
    @25
    @37
    @39
    @34
    wi
    @25
    @37
    wa
    #
    @28
    @38
    @19
    @33
    @40
    @38
    @28
    @25
    @14
    cz
    wcel
    @5
    cz
    wcel
    @38
    @28
    wb
    @37
    cZ
    cz
    @14
    @11
    sseli
    cZ
    cz
    @5
    @11
    sseli
    @14
    @5
    eluz
    syl2an
    biimprd
    @40
    @33
    @19
    @40
    @32
    @17
    @18
    clt
    @40
    @31
    @16
    cabs
    @37
    @25
    @29
    @6
    @30
    @15
    cmin
    vn
    @5
    @1
    @6
    cZ
    @2
    @0
    @5
    cF
    fveq2
    @2
    eqid
    #
    @0
    cF
    fvex
    #
    fvmpt3i
    vn
    @14
    @1
    @15
    cZ
    @2
    @0
    @14
    cF
    fveq2
    @41
    @42
    fvmpt3i
    oveqan12rd
    fveq2d
    breq1d
    biimprd
    imim12d
    ex
    com23
    ralimdv2
    reximia
    ralimi
    syl
    caucvgr
    wph
    cZ
    @2
    @12
    @27
    rlimdm
    mpbid
    syl5eqbr
    wph
    @3
    @7
    cM
    cZ
    caucvg.1
    @26
    wph
    vk
    cZ
    @6
    cc
    @7
    caucvg.2
    @7
    eqid
    #
    fmptd
    rlimclim
    mpbid
    wph
    @13
    cF
    cV
    wcel
    @4
    @8
    wb
    @26
    caucvg.4
    @3
    vk
    cF
    @7
    cM
    cV
    cZ
    caucvg.1
    @43
    climmpt
    syl2anc
    mpbird
    cF
    @3
    cli
    climrel
    releldmi
    syl
end
