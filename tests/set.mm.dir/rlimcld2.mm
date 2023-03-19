include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "csb.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "cc.mm"
include "cdif.mm"
include "crp.mm"
include "cmpt.mm"
include "crli.mm"
include "rlimcl.mm"
include "syl.mm"
include "simpr.mm"
include "eldifd.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "rlimi.mm"
include "adantlr.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfral.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "ad2antrr.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rspcv.mm"
include "rpred.mm"
include "wss.mm"
include "ad3antrrr.mm"
include "sseldd.mm"
include "subcld.mm"
include "abscld.mm"
include "lenltd.mm"
include "mpbid.mm"
include "id.mm"
include "imp.mm"
include "nsyl.mm"
include "nrexdv.mm"
include "cxr.mm"
include "csup.mm"
include "cpnf.mm"
include "wb.mm"
include "cdm.mm"
include "eqid.mm"
include "dmmptd.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrunb1.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "r19.29.mm"
include "expcom.mm"
include "mtod.mm"
include "condan.mm"

theorem rlimcld2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vr: setvar r
  let vw: setvar w
  assume rlimcld2.1: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimcld2.2: |- ( ph -> ( x e. A |-> B ) ~~>r C )
  assume rlimcld2.3: |- ( ph -> D C_ CC )
  assume rlimcld2.4: |- ( ( ph /\ y e. ( CC \ D ) ) -> R e. RR+ )
  assume rlimcld2.5: |- ( ( ( ph /\ y e. ( CC \ D ) ) /\ z e. D ) -> R <_ ( abs ` ( z - y ) ) )
  assume rlimcld2.6: |- ( ( ph /\ x e. A ) -> B e. D )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R x
  disjoint R z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint r w
  disjoint B r
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint C r
  disjoint w x
  disjoint C w
  disjoint ph r
  disjoint D r
  disjoint R r
  assert |- ( ph -> C e. D )

  proof
    wph
    cC
    cD
    wcel
    #
    vr
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cC
    cR
    csb
    #
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vr
    cr
    wrex
    wph
    @0
    wn
    #
    wa
    #
    vr
    vx
    cA
    cB
    cC
    @6
    cD
    wph
    cB
    cD
    wcel
    #
    vx
    cA
    wral
    @10
    wph
    @12
    vx
    cA
    rlimcld2.6
    ralrimiva
    adantr
    @11
    cC
    cc
    cD
    cdif
    #
    wcel
    #
    cR
    crp
    wcel
    #
    vy
    @13
    wral
    #
    @6
    crp
    wcel
    #
    @11
    cC
    cc
    cD
    @11
    vx
    cA
    cB
    cmpt
    #
    cC
    crli
    wbr
    #
    cC
    cc
    wcel
    #
    wph
    @19
    @10
    rlimcld2.2
    adantr
    #
    cC
    @18
    rlimcl
    syl
    #
    wph
    @10
    simpr
    eldifd
    #
    wph
    @16
    @10
    wph
    @15
    vy
    @13
    rlimcld2.4
    ralrimiva
    adantr
    @15
    @17
    vy
    cC
    @13
    vy
    @6
    crp
    vy
    cC
    cR
    nfcsb1v
    #
    nfel1
    vy
    cv
    #
    cC
    wceq
    #
    cR
    @6
    crp
    vy
    cC
    cR
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    #
    @21
    rlimi
    @11
    @9
    vr
    cr
    @11
    @1
    cr
    wcel
    #
    wa
    #
    @9
    @8
    @3
    wa
    #
    vx
    cA
    wrex
    #
    @30
    @31
    vx
    cA
    @30
    @2
    cA
    wcel
    #
    wa
    #
    @7
    @31
    @34
    @6
    @5
    cle
    wbr
    #
    @7
    wn
    @34
    @12
    @6
    vz
    cv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vz
    cD
    wral
    #
    @35
    @11
    @33
    @12
    @29
    wph
    @33
    @12
    @10
    rlimcld2.6
    adantlr
    adantlr
    #
    @11
    @40
    @29
    @33
    @11
    @14
    cR
    @36
    @25
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vz
    cD
    wral
    #
    vy
    @13
    wral
    #
    @40
    @23
    wph
    @46
    @10
    wph
    @45
    vy
    @13
    wph
    @25
    @13
    wcel
    wa
    @44
    vz
    cD
    rlimcld2.5
    ralrimiva
    ralrimiva
    adantr
    @45
    @40
    vy
    cC
    @13
    @39
    vy
    vz
    cD
    vy
    cD
    nfcv
    vy
    @6
    @38
    cle
    @24
    vy
    cle
    nfcv
    vy
    @38
    nfcv
    nfbr
    nfral
    @26
    @44
    @39
    vz
    cD
    @26
    cR
    @6
    @43
    @38
    cle
    @27
    @26
    @42
    @37
    cabs
    @25
    cC
    @36
    cmin
    oveq2
    fveq2d
    breq12d
    ralbidv
    rspc
    sylc
    ad2antrr
    @39
    @35
    vz
    cB
    cD
    @36
    cB
    wceq
    #
    @38
    @5
    @6
    cle
    @47
    @37
    @4
    cabs
    @36
    cB
    cC
    cmin
    oveq1
    fveq2d
    breq2d
    rspcv
    sylc
    @34
    @6
    @5
    @34
    @6
    @11
    @17
    @29
    @33
    @28
    ad2antrr
    rpred
    @34
    @4
    @34
    cB
    cC
    @34
    cD
    cc
    cB
    wph
    cD
    cc
    wss
    @10
    @29
    @33
    rlimcld2.3
    ad3antrrr
    @41
    sseldd
    @11
    @20
    @29
    @33
    @22
    ad2antrr
    subcld
    abscld
    lenltd
    mpbid
    @8
    @3
    @7
    @8
    id
    imp
    nsyl
    nrexdv
    @30
    @3
    vx
    cA
    wrex
    #
    @9
    @32
    wi
    @11
    @48
    vr
    cr
    wph
    @48
    vr
    cr
    wral
    #
    @10
    wph
    @49
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    rlimcld2.1
    wph
    cA
    cxr
    wss
    @49
    @50
    wb
    wph
    cA
    cr
    cxr
    wph
    cA
    @18
    cdm
    #
    cr
    wph
    vx
    @18
    cA
    cB
    cD
    @18
    eqid
    rlimcld2.6
    dmmptd
    wph
    @19
    @51
    cr
    wss
    rlimcld2.2
    cC
    @18
    rlimss
    syl
    eqsstr3d
    ressxr
    syl6ss
    vr
    vx
    cA
    supxrunb1
    syl
    mpbird
    adantr
    r19.21bi
    @9
    @48
    @32
    @8
    @3
    vx
    cA
    r19.29
    expcom
    syl
    mtod
    nrexdv
    condan
end
