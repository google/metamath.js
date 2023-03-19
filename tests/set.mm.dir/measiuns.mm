include "ciun.mm"
include "cfv.mm"
include "c1.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "cdif.mm"
include "cesum.mm"
include "iundisjcnt.mm"
include "fveq2d.mm"
include "cmeas.mm"
include "wcel.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wceq.mm"
include "wa.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "measbase.mm"
include "syl.mm"
include "adantr.mm"
include "simpll.mm"
include "cn.mm"
include "wss.mm"
include "fzossnn.mm"
include "simpr.mm"
include "syl5sseqr.mm"
include "cuz.mm"
include "simplr.mm"
include "eleqtrd.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "3syl.mm"
include "sseqtr4d.mm"
include "wo.mm"
include "mpjaodan.mm"
include "sselda.mm"
include "wsb.mm"
include "sbimi.mm"
include "sban.mm"
include "nfv.mm"
include "sbf.mm"
include "clelsb3.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wsbc.mm"
include "csb.mm"
include "sbsbc.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcel1g.mm"
include "ax-mp.mm"
include "nfcv.mm"
include "cbvcsb.mm"
include "csbid.mm"
include "eqtri.mm"
include "eleq1i.mm"
include "3bitri.mm"
include "3imtr3i.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "sigaclfu2.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "eqimss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "nnct.mm"
include "ssct.mm"
include "sylancl.mm"
include "iundisj2cnt.mm"
include "measvuni.mm"
include "syl112anc.mm"
include "eqtrd.mm"

theorem measiuns
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cI: class I
  let cM: class M
  let cN: class N
  assume measiuns.0: |- F/_ n B
  assume measiuns.1: |- ( n = k -> A = B )
  assume measiuns.2: |- ( ph -> ( N = NN \/ N = ( 1 ..^ I ) ) )
  assume measiuns.3: |- ( ph -> M e. ( measures ` S ) )
  assume measiuns.4: |- ( ( ph /\ n e. N ) -> A e. S )

  disjoint A k
  disjoint k n
  disjoint I k
  disjoint I n
  disjoint M n
  disjoint N k
  disjoint N n
  disjoint S k
  disjoint S n
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> ( M ` U_ n e. N A ) = sum* n e. N ( M ` ( A \ U_ k e. ( 1 ..^ n ) B ) ) )

  proof
    wph
    vn
    cN
    cA
    ciun
    #
    cM
    cfv
    vn
    cN
    cA
    vk
    c1
    vn
    cv
    #
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    ciun
    #
    cM
    cfv
    #
    cN
    @4
    cM
    cfv
    vn
    cesum
    #
    wph
    @0
    @5
    cM
    wph
    cA
    cB
    vk
    vn
    cI
    cN
    measiuns.0
    measiuns.1
    measiuns.2
    iundisjcnt
    fveq2d
    wph
    cM
    cS
    cmeas
    cfv
    wcel
    #
    @4
    cS
    wcel
    #
    vn
    cN
    wral
    cN
    com
    cdom
    wbr
    #
    vn
    cN
    @4
    wdisj
    @6
    @7
    wceq
    measiuns.3
    wph
    @9
    vn
    cN
    wph
    @1
    cN
    wcel
    #
    wa
    #
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    #
    @3
    cS
    wcel
    #
    @9
    wph
    @13
    @11
    wph
    @8
    @13
    measiuns.3
    cS
    cM
    measbase
    syl
    adantr
    #
    measiuns.4
    @12
    @13
    cB
    cS
    wcel
    #
    vk
    @2
    wral
    @15
    @16
    @12
    @17
    vk
    @2
    @12
    vk
    cv
    #
    @2
    wcel
    #
    wa
    wph
    @18
    cN
    wcel
    #
    @17
    wph
    @11
    @19
    simpll
    @12
    @2
    cN
    @18
    @12
    cN
    cn
    wceq
    #
    @2
    cN
    wss
    cN
    c1
    cI
    cfzo
    co
    #
    wceq
    #
    @12
    @21
    wa
    cn
    @2
    cN
    @1
    fzossnn
    @12
    @21
    simpr
    syl5sseqr
    @12
    @23
    wa
    #
    @2
    @22
    cN
    @24
    @1
    @22
    wcel
    cI
    @1
    cuz
    cfv
    wcel
    @2
    @22
    wss
    @24
    @1
    cN
    @22
    wph
    @11
    @23
    simplr
    @12
    @23
    simpr
    #
    eleqtrd
    @1
    c1
    cI
    elfzouz2
    @1
    c1
    cI
    fzoss2
    3syl
    @25
    sseqtr4d
    wph
    @21
    @23
    wo
    #
    @11
    measiuns.2
    adantr
    mpjaodan
    sselda
    @12
    vn
    vk
    wsb
    #
    @14
    vn
    vk
    wsb
    #
    wph
    @20
    wa
    #
    @17
    @12
    @14
    vn
    vk
    measiuns.4
    sbimi
    @27
    wph
    vn
    vk
    wsb
    #
    @11
    vn
    vk
    wsb
    #
    wa
    @29
    wph
    @11
    vn
    vk
    sban
    @30
    wph
    @31
    @20
    wph
    vn
    vk
    wph
    vn
    nfv
    sbf
    vk
    vn
    cN
    clelsb3
    anbi12i
    bitri
    @28
    @14
    vn
    @18
    wsbc
    #
    vn
    @18
    cA
    csb
    #
    cS
    wcel
    #
    @17
    @14
    vn
    vk
    sbsbc
    @18
    cvv
    wcel
    @32
    @34
    wb
    vk
    vex
    vn
    @18
    cA
    cS
    cvv
    sbcel1g
    ax-mp
    @33
    cB
    cS
    @33
    vk
    @18
    cB
    csb
    cB
    vn
    vk
    @18
    cA
    cB
    vk
    cA
    nfcv
    measiuns.0
    measiuns.1
    cbvcsb
    vk
    cB
    csbid
    eqtri
    eleq1i
    3bitri
    3imtr3i
    syl2anc
    ralrimiva
    cB
    cS
    vk
    @1
    sigaclfu2
    syl2anc
    cA
    @3
    cS
    difelsiga
    syl3anc
    ralrimiva
    wph
    cN
    cn
    wss
    #
    cn
    com
    cdom
    wbr
    @10
    wph
    @26
    @35
    measiuns.2
    @21
    @35
    @23
    cN
    cn
    eqimss
    @23
    @35
    @22
    cn
    wss
    cI
    fzossnn
    cN
    @22
    cn
    sseq1
    mpbiri
    jaoi
    syl
    nnct
    cN
    cn
    ssct
    sylancl
    wph
    cA
    cB
    vk
    vn
    cI
    cN
    measiuns.0
    measiuns.1
    measiuns.2
    iundisj2cnt
    vn
    cN
    @4
    cS
    cM
    measvuni
    syl112anc
    eqtrd
end
