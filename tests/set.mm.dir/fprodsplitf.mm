include "cprod.mm"
include "cv.mm"
include "csb.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvprod.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "fprodsplit.mm"
include "cbvprodi.mm"
include "oveq12i.mm"
include "eqcomi.mm"
include "3eqtrd.mm"

theorem fprodsplitf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  let vj: setvar j
  assume fprodsplitf.kph: |- F/ k ph
  assume fprodsplitf.in: |- ( ph -> ( A i^i B ) = (/) )
  assume fprodsplitf.un: |- ( ph -> U = ( A u. B ) )
  assume fprodsplitf.fi: |- ( ph -> U e. Fin )
  assume fprodsplitf.c: |- ( ( ph /\ k e. U ) -> C e. CC )

  disjoint A k
  disjoint B k
  disjoint U k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint U j
  disjoint j ph
  assert |- ( ph -> prod_ k e. U C = ( prod_ k e. A C x. prod_ k e. B C ) )

  proof
    wph
    cU
    cC
    vk
    cprod
    #
    cU
    vk
    vj
    cv
    #
    cC
    csb
    #
    vj
    cprod
    #
    cA
    @2
    vj
    cprod
    #
    cB
    @2
    vj
    cprod
    #
    cmul
    co
    #
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
    #
    @0
    @3
    wceq
    wph
    cU
    cC
    @2
    vk
    vj
    vk
    @1
    cC
    csbeq1a
    #
    vj
    cU
    nfcv
    vk
    cU
    nfcv
    vj
    cC
    nfcv
    #
    vk
    @1
    cC
    nfcsb1v
    #
    cbvprod
    a1i
    wph
    cA
    cB
    @2
    cU
    vj
    fprodsplitf.in
    fprodsplitf.un
    fprodsplitf.fi
    wph
    vk
    cv
    #
    cU
    wcel
    #
    wa
    #
    cC
    cc
    wcel
    #
    wi
    wph
    @1
    cU
    wcel
    #
    wa
    #
    @2
    cc
    wcel
    #
    wi
    vk
    vj
    @18
    @19
    vk
    wph
    @17
    vk
    fprodsplitf.kph
    @17
    vk
    nfv
    nfan
    vk
    @2
    cc
    @12
    nfel1
    nfim
    @13
    @1
    wceq
    #
    @15
    @18
    @16
    @19
    @20
    @14
    @17
    wph
    @13
    @1
    cU
    eleq1
    anbi2d
    @20
    cC
    @2
    cc
    @10
    eleq1d
    imbi12d
    fprodsplitf.c
    chvar
    fprodsplit
    @6
    @9
    wceq
    wph
    @9
    @6
    @7
    @4
    @8
    @5
    cmul
    cA
    cC
    @2
    vk
    vj
    @11
    @12
    @10
    cbvprodi
    cB
    cC
    @2
    vk
    vj
    @11
    @12
    @10
    cbvprodi
    oveq12i
    eqcomi
    a1i
    3eqtrd
end
