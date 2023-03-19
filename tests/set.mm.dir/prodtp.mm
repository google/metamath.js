include "ctp.mm"
include "cprod.mm"
include "cpr.mm"
include "csn.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjprsn.mm"
include "syl2anc.mm"
include "cun.mm"
include "df-tp.mm"
include "a1i.mm"
include "cfn.mm"
include "wcel.mm"
include "tpfi.mm"
include "cv.mm"
include "w3o.mm"
include "cc.mm"
include "vex.mm"
include "eltp.mm"
include "wa.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "simpr.mm"
include "mpjao3dan.mm"
include "sylan2b.mm"
include "fprodsplit.mm"
include "prodpr.mm"
include "prodsn.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem prodtp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  assume prodpr.1: |- ( k = A -> D = E )
  assume prodpr.2: |- ( k = B -> D = F )
  assume prodpr.a: |- ( ph -> A e. V )
  assume prodpr.b: |- ( ph -> B e. W )
  assume prodpr.e: |- ( ph -> E e. CC )
  assume prodpr.f: |- ( ph -> F e. CC )
  assume prodpr.3: |- ( ph -> A =/= B )
  assume prodtp.1: |- ( k = C -> D = G )
  assume prodtp.c: |- ( ph -> C e. X )
  assume prodtp.g: |- ( ph -> G e. CC )
  assume prodtp.2: |- ( ph -> A =/= C )
  assume prodtp.3: |- ( ph -> B =/= C )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint E k
  disjoint F k
  disjoint G k
  disjoint V k
  disjoint W k
  disjoint X k
  disjoint k ph
  assert |- ( ph -> prod_ k e. { A , B , C } D = ( ( E x. F ) x. G ) )

  proof
    wph
    cA
    cB
    cC
    ctp
    #
    cD
    vk
    cprod
    cA
    cB
    cpr
    #
    cD
    vk
    cprod
    #
    cC
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
    #
    cG
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
    cC
    wne
    cB
    cC
    wne
    @1
    @3
    cin
    c0
    wceq
    prodtp.2
    prodtp.3
    cA
    cB
    cC
    disjprsn
    syl2anc
    @0
    @1
    @3
    cun
    wceq
    wph
    cA
    cB
    cC
    df-tp
    a1i
    @0
    cfn
    wcel
    wph
    cA
    cB
    cC
    tpfi
    a1i
    vk
    cv
    #
    @0
    wcel
    wph
    @6
    cA
    wceq
    #
    @6
    cB
    wceq
    #
    @6
    cC
    wceq
    #
    w3o
    #
    cD
    cc
    wcel
    #
    @6
    cA
    cB
    cC
    vk
    vex
    eltp
    wph
    @10
    wa
    @7
    @11
    @8
    @9
    wph
    @7
    @11
    @10
    wph
    @7
    wa
    cD
    cE
    cc
    @7
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
    @7
    prodpr.e
    adantr
    eqeltrd
    adantlr
    wph
    @8
    @11
    @10
    wph
    @8
    wa
    cD
    cF
    cc
    @8
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
    @8
    prodpr.f
    adantr
    eqeltrd
    adantlr
    wph
    @9
    @11
    @10
    wph
    @9
    wa
    cD
    cG
    cc
    @9
    cD
    cG
    wceq
    wph
    prodtp.1
    adantl
    wph
    cG
    cc
    wcel
    #
    @9
    prodtp.g
    adantr
    eqeltrd
    adantlr
    wph
    @10
    simpr
    mpjao3dan
    sylan2b
    fprodsplit
    wph
    @2
    @5
    @4
    cG
    cmul
    wph
    cA
    cB
    cD
    vk
    cE
    cF
    cV
    cW
    prodpr.1
    prodpr.2
    prodpr.a
    prodpr.b
    prodpr.e
    prodpr.f
    prodpr.3
    prodpr
    wph
    cC
    cX
    wcel
    @12
    @4
    cG
    wceq
    prodtp.c
    prodtp.g
    cD
    cG
    vk
    cC
    cX
    prodtp.1
    prodsn
    syl2anc
    oveq12d
    eqtrd
end
