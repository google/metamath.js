include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "sge0reuz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "nfv.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "nfan.mm"
include "fzfid.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "sseldi.mm"
include "syldan.mm"
include "adantlr.mm"
include "fsumreclf.mm"
include "rnmptssd.mm"
include "cvv.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "eqidd.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sumex.mm"
include "a1i.mm"
include "elrnmptd.mm"
include "ne0i.mm"
include "wi.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "nfra1.mm"
include "rspa.mm"
include "simpr.mm"
include "simpl.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "rexlimd.mm"
include "adantr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "reximdai.mm"
include "supxrre.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem sge0reuzb
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume sge0reuzb.k: |- F/ k ph
  assume sge0reuzb.p: |- F/ x ph
  assume sge0reuzb.m: |- ( ph -> M e. ZZ )
  assume sge0reuzb.z: |- Z = ( ZZ>= ` M )
  assume sge0reuzb.b: |- ( ( ph /\ k e. Z ) -> B e. ( 0 [,) +oo ) )
  assume sge0reuzb.x: |- ( ph -> E. x e. RR A. n e. Z sum_ k e. ( M ... n ) B <_ x )

  disjoint B n
  disjoint B x
  disjoint n x
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint k n
  disjoint k x
  disjoint Z k
  disjoint Z n
  disjoint Z x
  disjoint n ph
  disjoint k x
  disjoint B y
  disjoint n y
  disjoint x y
  disjoint M y
  disjoint k y
  disjoint Z y
  disjoint ph y
  assert |- ( ph -> ( sum^ ` ( k e. Z |-> B ) ) = sup ( ran ( n e. Z |-> sum_ k e. ( M ... n ) B ) , RR , < ) )

  proof
    wph
    vk
    cZ
    cB
    cmpt
    csumge0
    cfv
    vn
    cZ
    cM
    vn
    cv
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @4
    cr
    clt
    csup
    #
    wph
    cB
    vk
    vn
    cM
    cZ
    sge0reuzb.k
    sge0reuzb.m
    sge0reuzb.z
    sge0reuzb.b
    sge0reuz
    wph
    @4
    cr
    wss
    @4
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    @4
    wral
    #
    vx
    cr
    wrex
    #
    @5
    @6
    wceq
    wph
    vn
    cZ
    @2
    cr
    @3
    wph
    vn
    nfv
    @3
    eqid
    #
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    cB
    vk
    wph
    @14
    vk
    sge0reuzb.k
    @14
    vk
    nfv
    nfan
    @15
    cM
    @0
    fzfid
    wph
    vk
    cv
    #
    @1
    wcel
    #
    cB
    cr
    wcel
    #
    @14
    wph
    @17
    @16
    cZ
    wcel
    #
    @18
    @17
    @19
    wph
    @17
    @16
    cM
    cuz
    cfv
    #
    cZ
    @16
    cM
    @0
    elfzuz
    sge0reuzb.z
    syl6eleqr
    adantl
    wph
    @19
    wa
    cc0
    cpnf
    cico
    co
    cr
    cB
    rge0ssre
    sge0reuzb.b
    sseldi
    syldan
    adantlr
    fsumreclf
    rnmptssd
    wph
    cM
    cM
    cfz
    co
    #
    cB
    vk
    csu
    #
    @4
    wcel
    @7
    wph
    vn
    cZ
    @2
    @22
    @3
    cvv
    @13
    wph
    cM
    cZ
    wcel
    @22
    @22
    wceq
    #
    @22
    @2
    wceq
    #
    vn
    cZ
    wrex
    wph
    cM
    @20
    cZ
    wph
    cM
    cz
    wcel
    cM
    @20
    wcel
    sge0reuzb.m
    cM
    uzid
    syl
    sge0reuzb.z
    syl6eleqr
    wph
    @22
    eqidd
    @24
    @23
    vn
    cM
    cZ
    @0
    cM
    wceq
    #
    @2
    @22
    @22
    @25
    @1
    @21
    cB
    vk
    @0
    cM
    cM
    cfz
    oveq2
    sumeq1d
    eqeq2d
    rspcev
    syl2anc
    @22
    cvv
    wcel
    wph
    @21
    cB
    vk
    sumex
    a1i
    elrnmptd
    @4
    @22
    ne0i
    syl
    wph
    @2
    @9
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    @12
    sge0reuzb.x
    wph
    @27
    @11
    vx
    cr
    sge0reuzb.p
    wph
    @9
    cr
    wcel
    #
    @27
    @11
    wi
    wph
    @28
    wa
    #
    @27
    @11
    @29
    @27
    wa
    #
    @10
    vy
    @4
    @30
    @8
    @4
    wcel
    #
    wa
    @8
    @2
    wceq
    #
    vn
    cZ
    wrex
    #
    @10
    @31
    @33
    @30
    @31
    @33
    @8
    cvv
    wcel
    @31
    @33
    wb
    vy
    vex
    vn
    cZ
    @2
    @8
    @3
    cvv
    @13
    elrnmpt
    ax-mp
    biimpi
    adantl
    @30
    @33
    @10
    wi
    @31
    @30
    @32
    @10
    vn
    cZ
    @29
    @27
    vn
    @29
    vn
    nfv
    @26
    vn
    cZ
    nfra1
    nfan
    @10
    vn
    nfv
    @27
    @14
    @32
    @10
    wi
    #
    wi
    @29
    @27
    @14
    @34
    @27
    @14
    wa
    @26
    @34
    @26
    vn
    cZ
    rspa
    @26
    @32
    @10
    @26
    @32
    wa
    @8
    @2
    @9
    cle
    @26
    @32
    simpr
    @26
    @32
    simpl
    eqbrtrd
    ex
    syl
    ex
    adantl
    rexlimd
    adantr
    mpd
    ralrimiva
    ex
    ex
    reximdai
    mpd
    vx
    vy
    @4
    supxrre
    syl3anc
    eqtrd
end
