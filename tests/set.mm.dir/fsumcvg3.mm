include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "adantr.mm"
include "syl6sseq.mm"
include "wor.mm"
include "cfn.mm"
include "w3a.mm"
include "ltso.mm"
include "simpr.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "3jca.mm"
include "fisupcl.mm"
include "sylancr.mm"
include "sseldd.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "fimaxre2.mm"
include "syl2anc.mm"
include "suprub.mm"
include "sylan.mm"
include "wb.mm"
include "sselda.mm"
include "sseldi.mm"
include "elfz5.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "uzid.mm"
include "syl.mm"
include "0ss.mm"
include "sylancl.mm"
include "pm2.61ne.mm"
include "cc0.mm"
include "cif.mm"
include "eleq2i.mm"
include "sylan2br.mm"
include "adantlr.mm"
include "simprl.mm"
include "cc.mm"
include "simprr.mm"
include "fsumcvg2.mm"
include "climrel.mm"
include "releldmi.mm"
include "rexlimddv.mm"

theorem fsumcvg3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vn: setvar n
  assume fsumcvg3.1: |- Z = ( ZZ>= ` M )
  assume fsumcvg3.2: |- ( ph -> M e. ZZ )
  assume fsumcvg3.3: |- ( ph -> A e. Fin )
  assume fsumcvg3.4: |- ( ph -> A C_ Z )
  assume fsumcvg3.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = if ( k e. A , B , 0 ) )
  assume fsumcvg3.6: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint k n
  disjoint A n
  disjoint F n
  disjoint M n
  disjoint n ph
  assert |- ( ph -> seq M ( + , F ) e. dom ~~> )

  proof
    wph
    cA
    cM
    vn
    cv
    #
    cfz
    co
    #
    wss
    #
    caddc
    cF
    cM
    cseq
    #
    cli
    cdm
    wcel
    #
    vn
    cM
    cuz
    cfv
    #
    wph
    @2
    vn
    @5
    wrex
    #
    c0
    @1
    wss
    #
    vn
    @5
    wrex
    #
    cA
    c0
    cA
    c0
    wceq
    @2
    @7
    vn
    @5
    cA
    c0
    @1
    sseq1
    rexbidv
    wph
    cA
    c0
    wne
    #
    wa
    #
    cA
    cr
    clt
    csup
    #
    @5
    wcel
    cA
    cM
    @11
    cfz
    co
    #
    wss
    #
    @6
    @10
    cA
    @5
    @11
    @10
    cA
    cZ
    @5
    wph
    cA
    cZ
    wss
    @9
    fsumcvg3.4
    adantr
    #
    fsumcvg3.1
    syl6sseq
    #
    @10
    cr
    clt
    wor
    cA
    cfn
    wcel
    #
    @9
    cA
    cr
    wss
    #
    w3a
    @11
    cA
    wcel
    ltso
    @10
    @16
    @9
    @17
    wph
    @16
    @9
    fsumcvg3.3
    adantr
    #
    wph
    @9
    simpr
    #
    @10
    cA
    cZ
    cr
    @14
    cZ
    @5
    cr
    fsumcvg3.1
    @5
    cz
    cr
    cM
    uzssz
    #
    zssre
    sstri
    eqsstri
    syl6ss
    #
    3jca
    cr
    cA
    clt
    fisupcl
    sylancr
    sseldd
    #
    @10
    vk
    cA
    @12
    @10
    vk
    cv
    #
    cA
    wcel
    #
    @23
    @12
    wcel
    #
    @10
    @24
    wa
    #
    @25
    @23
    @11
    cle
    wbr
    #
    @10
    @17
    @9
    @0
    @23
    cle
    wbr
    vn
    cA
    wral
    vk
    cr
    wrex
    #
    w3a
    @24
    @27
    @10
    @17
    @9
    @28
    @21
    @19
    @10
    @17
    @16
    @28
    @21
    @18
    vk
    vn
    cA
    fimaxre2
    syl2anc
    3jca
    vk
    vn
    cA
    @23
    suprub
    sylan
    @26
    @23
    @5
    wcel
    #
    @11
    cz
    wcel
    #
    @25
    @27
    wb
    @10
    cA
    @5
    @23
    @15
    sselda
    @10
    @30
    @24
    @10
    @5
    cz
    @11
    @20
    @22
    sseldi
    adantr
    @23
    cM
    @11
    elfz5
    syl2anc
    mpbird
    ex
    ssrdv
    @2
    @13
    vn
    @11
    @5
    @0
    @11
    wceq
    @1
    @12
    cA
    @0
    @11
    cM
    cfz
    oveq2
    sseq2d
    rspcev
    syl2anc
    wph
    cM
    @5
    wcel
    #
    c0
    cM
    cM
    cfz
    co
    #
    wss
    #
    @8
    wph
    cM
    cz
    wcel
    @31
    fsumcvg3.2
    cM
    uzid
    syl
    @32
    0ss
    @7
    @33
    vn
    cM
    @5
    @0
    cM
    wceq
    @1
    @32
    c0
    @0
    cM
    cM
    cfz
    oveq2
    sseq2d
    rspcev
    sylancl
    pm2.61ne
    wph
    @0
    @5
    wcel
    #
    @2
    wa
    #
    wa
    #
    @3
    @0
    @3
    cfv
    #
    cli
    wbr
    @4
    @36
    cA
    cB
    vk
    cF
    cM
    @0
    wph
    @29
    @23
    cF
    cfv
    @24
    cB
    cc0
    cif
    wceq
    #
    @35
    @29
    wph
    @23
    cZ
    wcel
    @38
    cZ
    @5
    @23
    fsumcvg3.1
    eleq2i
    fsumcvg3.5
    sylan2br
    adantlr
    wph
    @34
    @2
    simprl
    wph
    @24
    cB
    cc
    wcel
    @35
    fsumcvg3.6
    adantlr
    wph
    @34
    @2
    simprr
    fsumcvg2
    @3
    @37
    cli
    climrel
    releldmi
    syl
    rexlimddv
end
