include "cpr.mm"
include "cprod.mm"
include "csn.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn2.mm"
include "syl.mm"
include "cun.mm"
include "df-pr.mm"
include "a1i.mm"
include "cfn.mm"
include "wcel.mm"
include "prfi.mm"
include "cv.mm"
include "wo.mm"
include "cc.mm"
include "vex.mm"
include "elpr.mm"
include "wa.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "fprodsplit.mm"
include "prodsn.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem prodpr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let cC: class C
  let cG: class G
  let cX: class X
  assume prodpr.1: |- ( k = A -> D = E )
  assume prodpr.2: |- ( k = B -> D = F )
  assume prodpr.a: |- ( ph -> A e. V )
  assume prodpr.b: |- ( ph -> B e. W )
  assume prodpr.e: |- ( ph -> E e. CC )
  assume prodpr.f: |- ( ph -> F e. CC )
  assume prodpr.3: |- ( ph -> A =/= B )

  disjoint A k
  disjoint B k
  disjoint E k
  disjoint F k
  disjoint V k
  disjoint W k
  disjoint k ph
  disjoint C k
  disjoint G k
  disjoint X k
  assert |- ( ph -> prod_ k e. { A , B } D = ( E x. F ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cD
    vk
    cprod
    cA
    csn
    #
    cD
    vk
    cprod
    #
    cB
    csn
    #
    cD
    vk
    cprod
    #
    cmul
    co
    cE
    cF
    cmul
    co
    wph
    @1
    @3
    cD
    @0
    vk
    wph
    cA
    cB
    wne
    @1
    @3
    cin
    c0
    wceq
    prodpr.3
    cA
    cB
    disjsn2
    syl
    @0
    @1
    @3
    cun
    wceq
    wph
    cA
    cB
    df-pr
    a1i
    @0
    cfn
    wcel
    wph
    cA
    cB
    prfi
    a1i
    vk
    cv
    #
    @0
    wcel
    wph
    @5
    cA
    wceq
    #
    @5
    cB
    wceq
    #
    wo
    cD
    cc
    wcel
    #
    @5
    cA
    cB
    vk
    vex
    elpr
    wph
    @6
    @8
    @7
    wph
    @6
    wa
    cD
    cE
    cc
    @6
    cD
    cE
    wceq
    wph
    prodpr.1
    adantl
    wph
    cE
    cc
    wcel
    #
    @6
    prodpr.e
    adantr
    eqeltrd
    wph
    @7
    wa
    cD
    cF
    cc
    @7
    cD
    cF
    wceq
    wph
    prodpr.2
    adantl
    wph
    cF
    cc
    wcel
    #
    @7
    prodpr.f
    adantr
    eqeltrd
    jaodan
    sylan2b
    fprodsplit
    wph
    @2
    cE
    @4
    cF
    cmul
    wph
    cA
    cV
    wcel
    @9
    @2
    cE
    wceq
    prodpr.a
    prodpr.e
    cD
    cE
    vk
    cA
    cV
    prodpr.1
    prodsn
    syl2anc
    wph
    cB
    cW
    wcel
    @10
    @4
    cF
    wceq
    prodpr.b
    prodpr.f
    cD
    cF
    vk
    cB
    cW
    prodpr.2
    prodsn
    syl2anc
    oveq12d
    eqtrd
end
