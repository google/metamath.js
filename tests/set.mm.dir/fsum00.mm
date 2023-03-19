include "csu.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "csn.mm"
include "cfn.mm"
include "adantr.mm"
include "cr.mm"
include "adantlr.mm"
include "wss.mm"
include "snssi.mm"
include "adantl.mm"
include "fsumless.mm"
include "cc.mm"
include "simpr.mm"
include "jca.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfan.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "simpld.mm"
include "recnd.mm"
include "sumsns.mm"
include "syl2anc.mm"
include "simplr.mm"
include "3brtr3d.mm"
include "simprd.mm"
include "wb.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "nfv.mm"
include "nfeq1.mm"
include "eqeq1d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "ex.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "sumz.mm"
include "olcs.mm"
include "sumeq2.mm"
include "syl5ibrcom.mm"
include "syl.mm"
include "impbid.mm"

theorem fsum00
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cM: class M
  assume fsumge0.1: |- ( ph -> A e. Fin )
  assume fsumge0.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumge0.3: |- ( ( ph /\ k e. A ) -> 0 <_ B )

  disjoint A k
  disjoint k ph
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint C k
  disjoint M k
  disjoint m ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( sum_ k e. A B = 0 <-> A. k e. A B = 0 ) )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    vk
    cA
    wral
    #
    wph
    @1
    @3
    wph
    @1
    wa
    #
    vk
    vm
    cv
    #
    cB
    csb
    #
    cc0
    wceq
    #
    vm
    cA
    wral
    @3
    @4
    @7
    vm
    cA
    @4
    @5
    cA
    wcel
    #
    wa
    #
    @7
    @6
    cc0
    cle
    wbr
    #
    cc0
    @6
    cle
    wbr
    #
    @9
    @5
    csn
    #
    cB
    vk
    csu
    #
    @0
    @6
    cc0
    cle
    wph
    @8
    @13
    @0
    cle
    wbr
    @1
    wph
    @8
    wa
    cA
    cB
    @12
    vk
    wph
    cA
    cfn
    wcel
    #
    @8
    fsumge0.1
    adantr
    wph
    vk
    cv
    #
    cA
    wcel
    #
    cB
    cr
    wcel
    #
    @8
    fsumge0.2
    adantlr
    wph
    @16
    cc0
    cB
    cle
    wbr
    #
    @8
    fsumge0.3
    adantlr
    @8
    @12
    cA
    wss
    wph
    @5
    cA
    snssi
    adantl
    fsumless
    adantlr
    @9
    @8
    @6
    cc
    wcel
    @13
    @6
    wceq
    @4
    @8
    simpr
    @9
    @6
    @9
    @6
    cr
    wcel
    #
    @11
    @4
    @17
    @18
    wa
    #
    vk
    cA
    wral
    #
    @8
    @19
    @11
    wa
    #
    wph
    @21
    @1
    wph
    @20
    vk
    cA
    wph
    @16
    wa
    @17
    @18
    fsumge0.2
    fsumge0.3
    jca
    ralrimiva
    adantr
    @20
    @22
    vk
    @5
    cA
    @19
    @11
    vk
    vk
    @6
    cr
    vk
    @5
    cB
    nfcsb1v
    #
    nfel1
    vk
    cc0
    @6
    cle
    vk
    cc0
    nfcv
    vk
    cle
    nfcv
    @23
    nfbr
    nfan
    @15
    @5
    wceq
    #
    @17
    @19
    @18
    @11
    @24
    cB
    @6
    cr
    vk
    @5
    cB
    csbeq1a
    #
    eleq1d
    @24
    cB
    @6
    cc0
    cle
    @25
    breq2d
    anbi12d
    rspc
    mpan9
    #
    simpld
    #
    recnd
    cB
    vk
    @5
    cA
    sumsns
    syl2anc
    wph
    @1
    @8
    simplr
    3brtr3d
    @9
    @19
    @11
    @26
    simprd
    @9
    @19
    cc0
    cr
    wcel
    @7
    @10
    @11
    wa
    wb
    @27
    0re
    @6
    cc0
    letri3
    sylancl
    mpbir2and
    ralrimiva
    @2
    @7
    vk
    vm
    cA
    @2
    vm
    nfv
    vk
    @6
    cc0
    @23
    nfeq1
    @24
    cB
    @6
    cc0
    @25
    eqeq1d
    cbvral
    sylibr
    ex
    wph
    @14
    @3
    @1
    wi
    fsumge0.1
    @14
    @1
    @3
    cA
    cc0
    vk
    csu
    #
    cc0
    wceq
    #
    cA
    cc0
    cuz
    cfv
    wss
    @14
    @29
    cA
    vk
    cc0
    sumz
    olcs
    @3
    @0
    @28
    cc0
    cA
    cB
    cc0
    vk
    sumeq2
    eqeq1d
    syl5ibrcom
    syl
    impbid
end
