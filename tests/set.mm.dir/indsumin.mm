include "cv.mm"
include "cind.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "cc0.mm"
include "c0.mm"
include "wceq.mm"
include "inindif.mm"
include "a1i.mm"
include "cun.mm"
include "inundif.mm"
include "eqcomi.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cpr.mm"
include "cc.mm"
include "cr.mm"
include "pr01ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "wf.mm"
include "wss.mm"
include "indf.mm"
include "syl2anc.mm"
include "adantr.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "mulcld.mm"
include "fsumsplit.mm"
include "inss2.mm"
include "ind1.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "inss1.mm"
include "syldan.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "ssdifd.mm"
include "ind0.mm"
include "difssd.mm"
include "mul02d.mm"
include "cfn.mm"
include "diffi.mm"
include "syl.mm"
include "cuz.mm"
include "sumz.mm"
include "olcs.mm"
include "oveq12d.mm"
include "infi.mm"
include "fsumcl.mm"
include "addid1d.mm"
include "3eqtrd.mm"

theorem indsumin
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cO: class O
  let cV: class V
  assume indsumin.1: |- ( ph -> O e. V )
  assume indsumin.2: |- ( ph -> A e. Fin )
  assume indsumin.3: |- ( ph -> A C_ O )
  assume indsumin.4: |- ( ph -> B C_ O )
  assume indsumin.5: |- ( ( ph /\ k e. A ) -> C e. CC )

  disjoint A k
  disjoint B k
  disjoint O k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A ( ( ( ( _Ind ` O ) ` B ) ` k ) x. C ) = sum_ k e. ( A i^i B ) C )

  proof
    wph
    cA
    vk
    cv
    #
    cB
    cO
    cind
    cfv
    cfv
    #
    cfv
    #
    cC
    cmul
    co
    #
    vk
    csu
    cA
    cB
    cin
    #
    @3
    vk
    csu
    #
    cA
    cB
    cdif
    #
    @3
    vk
    csu
    #
    caddc
    co
    @4
    cC
    vk
    csu
    #
    cc0
    caddc
    co
    @8
    wph
    @4
    @6
    @3
    cA
    vk
    @4
    @6
    cin
    c0
    wceq
    wph
    cA
    cB
    inindif
    a1i
    cA
    @4
    @6
    cun
    #
    wceq
    wph
    @9
    cA
    cA
    cB
    inundif
    eqcomi
    a1i
    indsumin.2
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @2
    cC
    @11
    cc0
    c1
    cpr
    #
    cc
    @2
    @12
    cr
    cc
    pr01ssre
    ax-resscn
    sstri
    @11
    cO
    @12
    @0
    @1
    wph
    cO
    @12
    @1
    wf
    #
    @10
    wph
    cO
    cV
    wcel
    #
    cB
    cO
    wss
    #
    @13
    indsumin.1
    indsumin.4
    cB
    cO
    cV
    indf
    syl2anc
    adantr
    wph
    cA
    cO
    @0
    indsumin.3
    sselda
    ffvelrnd
    sseldi
    indsumin.5
    mulcld
    fsumsplit
    wph
    @5
    @8
    @7
    cc0
    caddc
    wph
    @4
    @3
    cC
    vk
    wph
    @0
    @4
    wcel
    #
    wa
    #
    @3
    c1
    cC
    cmul
    co
    cC
    @17
    @2
    c1
    cC
    cmul
    @17
    @14
    @15
    @0
    cB
    wcel
    @2
    c1
    wceq
    wph
    @14
    @16
    indsumin.1
    adantr
    wph
    @15
    @16
    indsumin.4
    adantr
    wph
    @4
    cB
    @0
    @4
    cB
    wss
    wph
    cA
    cB
    inss2
    a1i
    sselda
    cB
    cO
    cV
    @0
    ind1
    syl3anc
    oveq1d
    @17
    cC
    wph
    @16
    @10
    cC
    cc
    wcel
    #
    wph
    @4
    cA
    @0
    @4
    cA
    wss
    wph
    cA
    cB
    inss1
    a1i
    sselda
    indsumin.5
    syldan
    #
    mulid2d
    eqtrd
    sumeq2dv
    wph
    @7
    @6
    cc0
    vk
    csu
    #
    cc0
    wph
    @6
    @3
    cc0
    vk
    wph
    @0
    @6
    wcel
    #
    wa
    #
    @3
    cc0
    cC
    cmul
    co
    cc0
    @22
    @2
    cc0
    cC
    cmul
    @22
    @14
    @15
    @0
    cO
    cB
    cdif
    #
    wcel
    @2
    cc0
    wceq
    wph
    @14
    @21
    indsumin.1
    adantr
    wph
    @15
    @21
    indsumin.4
    adantr
    wph
    @6
    @23
    @0
    wph
    cA
    cO
    cB
    indsumin.3
    ssdifd
    sselda
    cB
    cO
    cV
    @0
    ind0
    syl3anc
    oveq1d
    @22
    cC
    wph
    @21
    @10
    @18
    wph
    @6
    cA
    @0
    wph
    cA
    cB
    difssd
    sselda
    indsumin.5
    syldan
    mul02d
    eqtrd
    sumeq2dv
    wph
    @6
    cfn
    wcel
    #
    @20
    cc0
    wceq
    #
    wph
    cA
    cfn
    wcel
    #
    @24
    indsumin.2
    cA
    cB
    diffi
    syl
    @6
    cc0
    cuz
    cfv
    wss
    @24
    @25
    @6
    vk
    cc0
    sumz
    olcs
    syl
    eqtrd
    oveq12d
    wph
    @8
    wph
    @4
    cC
    vk
    wph
    @26
    @4
    cfn
    wcel
    indsumin.2
    cA
    cB
    infi
    syl
    @19
    fsumcl
    addid1d
    3eqtrd
end
