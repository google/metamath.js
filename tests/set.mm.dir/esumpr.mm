include "cpr.mm"
include "cesum.mm"
include "csn.mm"
include "cun.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "df-pr.mm"
include "esumeq1.mm"
include "mp1i.mm"
include "nfv.mm"
include "nfcv.mm"
include "cvv.mm"
include "wcel.mm"
include "snex.mm"
include "a1i.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "disjsn2.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "elsni.mm"
include "sylan2.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "esumsplit.mm"
include "esumsn.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem esumpr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  assume esumpr.1: |- ( ( ph /\ k = A ) -> C = D )
  assume esumpr.2: |- ( ( ph /\ k = B ) -> C = E )
  assume esumpr.3: |- ( ph -> A e. V )
  assume esumpr.4: |- ( ph -> B e. W )
  assume esumpr.5: |- ( ph -> D e. ( 0 [,] +oo ) )
  assume esumpr.6: |- ( ph -> E e. ( 0 [,] +oo ) )
  assume esumpr.7: |- ( ph -> A =/= B )

  disjoint A k
  disjoint B k
  disjoint D k
  disjoint E k
  disjoint k ph
  disjoint V k
  disjoint W k
  assert |- ( ph -> sum* k e. { A , B } C = ( D +e E ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cC
    vk
    cesum
    #
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    cC
    vk
    cesum
    #
    @2
    cC
    vk
    cesum
    #
    @3
    cC
    vk
    cesum
    #
    cxad
    co
    cD
    cE
    cxad
    co
    @0
    @4
    wceq
    @1
    @5
    wceq
    wph
    cA
    cB
    df-pr
    @0
    @4
    cC
    vk
    esumeq1
    mp1i
    wph
    @2
    @3
    cC
    vk
    wph
    vk
    nfv
    vk
    @2
    nfcv
    vk
    @3
    nfcv
    @2
    cvv
    wcel
    wph
    cA
    snex
    a1i
    @3
    cvv
    wcel
    wph
    cB
    snex
    a1i
    wph
    cA
    cB
    wne
    @2
    @3
    cin
    c0
    wceq
    esumpr.7
    cA
    cB
    disjsn2
    syl
    wph
    vk
    cv
    #
    @2
    wcel
    #
    wa
    cC
    cD
    cc0
    cpnf
    cicc
    co
    #
    @9
    wph
    @8
    cA
    wceq
    cC
    cD
    wceq
    @8
    cA
    elsni
    esumpr.1
    sylan2
    wph
    cD
    @10
    wcel
    @9
    esumpr.5
    adantr
    eqeltrd
    wph
    @8
    @3
    wcel
    #
    wa
    cC
    cE
    @10
    @11
    wph
    @8
    cB
    wceq
    cC
    cE
    wceq
    @8
    cB
    elsni
    esumpr.2
    sylan2
    wph
    cE
    @10
    wcel
    @11
    esumpr.6
    adantr
    eqeltrd
    esumsplit
    wph
    @6
    cD
    @7
    cE
    cxad
    wph
    cC
    cD
    vk
    cA
    cV
    esumpr.1
    esumpr.3
    esumpr.5
    esumsn
    wph
    cC
    cE
    vk
    cB
    cW
    esumpr.2
    esumpr.4
    esumpr.6
    esumsn
    oveq12d
    3eqtrd
end
