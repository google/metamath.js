include "cprod.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "cif.mm"
include "iftrue.mm"
include "prodeq2i.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "adantl.mm"
include "sselda.mm"
include "syldan.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "fprodss.mm"
include "syl5eqr.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "ax-1cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fprodmul.mm"
include "wo.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "cin.mm"
include "c0.mm"
include "wn.mm"
include "disjel.mm"
include "sylan.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "ex.mm"
include "con2d.mm"
include "imp.mm"
include "mulid2d.mm"
include "jaodan.mm"
include "prodeq2dv.mm"
include "3eqtr2rd.mm"

theorem fprodsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  assume fprodsplit.1: |- ( ph -> ( A i^i B ) = (/) )
  assume fprodsplit.2: |- ( ph -> U = ( A u. B ) )
  assume fprodsplit.3: |- ( ph -> U e. Fin )
  assume fprodsplit.4: |- ( ( ph /\ k e. U ) -> C e. CC )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint U k
  assert |- ( ph -> prod_ k e. U C = ( prod_ k e. A C x. prod_ k e. B C ) )

  proof
    wph
    cA
    cC
    vk
    cprod
    #
    cB
    cC
    vk
    cprod
    #
    cmul
    co
    cU
    vk
    cv
    #
    cA
    wcel
    #
    cC
    c1
    cif
    #
    vk
    cprod
    #
    cU
    @2
    cB
    wcel
    #
    cC
    c1
    cif
    #
    vk
    cprod
    #
    cmul
    co
    cU
    @4
    @7
    cmul
    co
    #
    vk
    cprod
    cU
    cC
    vk
    cprod
    wph
    @0
    @5
    @1
    @8
    cmul
    wph
    @0
    cA
    @4
    vk
    cprod
    @5
    cA
    @4
    cC
    vk
    @3
    cC
    c1
    iftrue
    #
    prodeq2i
    wph
    cA
    cU
    @4
    vk
    wph
    cA
    cB
    cun
    #
    cA
    cU
    cA
    cB
    ssun1
    fprodsplit.2
    syl5sseqr
    #
    wph
    @3
    wa
    #
    @4
    cC
    cc
    @3
    @4
    cC
    wceq
    wph
    @10
    adantl
    #
    wph
    @3
    @2
    cU
    wcel
    #
    cC
    cc
    wcel
    #
    wph
    cA
    cU
    @2
    @12
    sselda
    fprodsplit.4
    syldan
    #
    eqeltrd
    @2
    cU
    cA
    cdif
    wcel
    #
    @4
    c1
    wceq
    wph
    @18
    @3
    cC
    c1
    @2
    cU
    cA
    eldifn
    iffalsed
    adantl
    fprodsplit.3
    fprodss
    syl5eqr
    wph
    @1
    cB
    @7
    vk
    cprod
    @8
    cB
    @7
    cC
    vk
    @6
    cC
    c1
    iftrue
    #
    prodeq2i
    wph
    cB
    cU
    @7
    vk
    wph
    @11
    cB
    cU
    cB
    cA
    ssun2
    fprodsplit.2
    syl5sseqr
    #
    wph
    @6
    wa
    #
    @7
    cC
    cc
    @6
    @7
    cC
    wceq
    wph
    @19
    adantl
    #
    wph
    @6
    @15
    @16
    wph
    cB
    cU
    @2
    @20
    sselda
    fprodsplit.4
    syldan
    #
    eqeltrd
    @2
    cU
    cB
    cdif
    wcel
    #
    @7
    c1
    wceq
    wph
    @24
    @6
    cC
    c1
    @2
    cU
    cB
    eldifn
    iffalsed
    adantl
    fprodsplit.3
    fprodss
    syl5eqr
    oveq12d
    wph
    cU
    @4
    @7
    vk
    fprodsplit.3
    wph
    @15
    wa
    #
    @16
    c1
    cc
    wcel
    #
    @4
    cc
    wcel
    fprodsplit.4
    ax-1cn
    @3
    cC
    c1
    cc
    ifcl
    sylancl
    @25
    @16
    @26
    @7
    cc
    wcel
    fprodsplit.4
    ax-1cn
    @6
    cC
    c1
    cc
    ifcl
    sylancl
    fprodmul
    wph
    cU
    @9
    cC
    vk
    wph
    @15
    @3
    @6
    wo
    #
    @9
    cC
    wceq
    #
    wph
    @15
    @27
    wph
    @15
    @2
    @11
    wcel
    @27
    wph
    cU
    @11
    @2
    fprodsplit.2
    eleq2d
    @2
    cA
    cB
    elun
    syl6bb
    biimpa
    wph
    @3
    @28
    @6
    @13
    @9
    cC
    c1
    cmul
    co
    cC
    @13
    @4
    cC
    @7
    c1
    cmul
    @14
    @13
    @6
    cC
    c1
    wph
    cA
    cB
    cin
    c0
    wceq
    @3
    @6
    wn
    #
    fprodsplit.1
    cA
    cB
    @2
    disjel
    sylan
    #
    iffalsed
    oveq12d
    @13
    cC
    @17
    mulid1d
    eqtrd
    @21
    @9
    c1
    cC
    cmul
    co
    cC
    @21
    @4
    c1
    @7
    cC
    cmul
    @21
    @3
    cC
    c1
    wph
    @6
    @3
    wn
    wph
    @3
    @6
    wph
    @3
    @29
    @30
    ex
    con2d
    imp
    iffalsed
    @22
    oveq12d
    @21
    cC
    @23
    mulid2d
    eqtrd
    jaodan
    syldan
    prodeq2dv
    3eqtr2rd
end
