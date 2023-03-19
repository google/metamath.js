include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crli.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "wceq.mm"
include "fcompt.mm"
include "sylancr.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "clsp.mm"
include "fco.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "syl2anc.mm"
include "ffvelrni.mm"
include "syl.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "subcld.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "fvco3.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "sylibrd.mm"
include "imim2d.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "caurcvgr.mm"
include "rlimrel.mm"
include "releldmi.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "rlimdm.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"

theorem caucvgrlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  assume caucvgr.1: |- ( ph -> A C_ RR )
  assume caucvgr.2: |- ( ph -> F : A --> CC )
  assume caucvgr.3: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume caucvgr.4: |- ( ph -> A. x e. RR+ E. j e. A A. k e. A ( j <_ k -> ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) )
  assume caucvgrlem2.5: |- H : CC --> RR
  assume caucvgrlem2.6: |- ( ( ( F ` k ) e. CC /\ ( F ` j ) e. CC ) -> ( abs ` ( ( H ` ( F ` k ) ) - ( H ` ( F ` j ) ) ) ) <_ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) )

  disjoint j k
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint H j
  disjoint H k
  disjoint H n
  disjoint H x
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( n e. A |-> ( H ` ( F ` n ) ) ) ~~>r ( ~~>r ` ( H o. F ) ) )

  proof
    wph
    cH
    cF
    ccom
    #
    vn
    cA
    vn
    cv
    cF
    cfv
    cH
    cfv
    cmpt
    #
    @0
    crli
    cfv
    #
    crli
    wph
    cc
    cr
    cH
    wf
    #
    cA
    cc
    cF
    wf
    #
    @0
    @1
    wceq
    caucvgrlem2.5
    caucvgr.2
    vn
    cH
    cF
    cA
    cc
    cr
    fcompt
    sylancr
    wph
    @0
    crli
    cdm
    wcel
    #
    @0
    @2
    crli
    wbr
    wph
    @0
    @0
    clsp
    cfv
    #
    crli
    wbr
    @5
    wph
    vx
    cA
    vj
    vk
    @0
    caucvgr.1
    wph
    @3
    @4
    cA
    cr
    @0
    wf
    #
    caucvgrlem2.5
    caucvgr.2
    cA
    cc
    cr
    cH
    cF
    fco
    sylancr
    #
    caucvgr.3
    wph
    vj
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    @10
    cF
    cfv
    #
    @9
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
    wi
    #
    vk
    cA
    wral
    #
    vj
    cA
    wrex
    #
    vx
    crp
    wral
    @11
    @10
    @0
    cfv
    #
    @9
    @0
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    wi
    #
    vk
    cA
    wral
    #
    vj
    cA
    wrex
    #
    vx
    crp
    wral
    caucvgr.4
    wph
    @20
    @28
    vx
    crp
    wph
    @16
    crp
    wcel
    #
    wa
    #
    @19
    @27
    vj
    cA
    @30
    @9
    cA
    wcel
    #
    wa
    @18
    @26
    vk
    cA
    @30
    @31
    @10
    cA
    wcel
    #
    @18
    @26
    wi
    @30
    @31
    @32
    wa
    #
    wa
    #
    @17
    @25
    @11
    @34
    @17
    @12
    cH
    cfv
    #
    @13
    cH
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    @25
    @34
    @38
    @15
    cle
    wbr
    #
    @17
    @39
    @34
    @12
    cc
    wcel
    #
    @13
    cc
    wcel
    #
    @40
    @34
    cA
    cc
    @10
    cF
    wph
    @4
    @29
    @33
    caucvgr.2
    ad2antrr
    #
    @30
    @31
    @32
    simprr
    #
    ffvelrnd
    #
    @34
    cA
    cc
    @9
    cF
    @43
    @30
    @31
    @32
    simprl
    #
    ffvelrnd
    #
    caucvgrlem2.6
    syl2anc
    @34
    @38
    cr
    wcel
    @15
    cr
    wcel
    @16
    cr
    wcel
    #
    @40
    @17
    wa
    @39
    wi
    @34
    @37
    @34
    @37
    @34
    @35
    @36
    @34
    @41
    @35
    cr
    wcel
    @45
    cc
    cr
    @12
    cH
    caucvgrlem2.5
    ffvelrni
    syl
    @34
    @42
    @36
    cr
    wcel
    @47
    cc
    cr
    @13
    cH
    caucvgrlem2.5
    ffvelrni
    syl
    resubcld
    recnd
    abscld
    @34
    @14
    @34
    @12
    @13
    @45
    @47
    subcld
    abscld
    @29
    @48
    wph
    @33
    @16
    rpre
    ad2antlr
    @38
    @15
    @16
    lelttr
    syl3anc
    mpand
    @34
    @24
    @38
    @16
    clt
    @34
    @23
    @37
    cabs
    @34
    @21
    @35
    @22
    @36
    cmin
    @34
    @4
    @32
    @21
    @35
    wceq
    @43
    @44
    cA
    cc
    @10
    cH
    cF
    fvco3
    syl2anc
    @34
    @4
    @31
    @22
    @36
    wceq
    @43
    @46
    cA
    cc
    @9
    cH
    cF
    fvco3
    syl2anc
    oveq12d
    fveq2d
    breq1d
    sylibrd
    imim2d
    anassrs
    ralimdva
    reximdva
    ralimdva
    mpd
    caurcvgr
    @0
    @6
    crli
    rlimrel
    releldmi
    syl
    wph
    cA
    @0
    wph
    @7
    cr
    cc
    wss
    cA
    cc
    @0
    wf
    @8
    ax-resscn
    cA
    cr
    cc
    @0
    fss
    sylancl
    caucvgr.3
    rlimdm
    mpbid
    eqbrtrrd
end
