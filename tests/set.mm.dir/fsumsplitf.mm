include "csu.mm"
include "cv.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvsum.mm"
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
include "fsumsplit.mm"
include "csbco.mm"
include "csbid.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "eqid.mm"
include "cbvsumi.mm"
include "oveq12i.mm"
include "3eqtrd.mm"

theorem fsumsplitf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  let vj: setvar j
  assume fsumsplitf.ph: |- F/ k ph
  assume fsumsplitf.ab: |- ( ph -> ( A i^i B ) = (/) )
  assume fsumsplitf.u: |- ( ph -> U = ( A u. B ) )
  assume fsumsplitf.fi: |- ( ph -> U e. Fin )
  assume fsumsplitf.c: |- ( ( ph /\ k e. U ) -> C e. CC )

  disjoint A k
  disjoint B k
  disjoint U k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint U j
  disjoint j ph
  assert |- ( ph -> sum_ k e. U C = ( sum_ k e. A C + sum_ k e. B C ) )

  proof
    wph
    cU
    cC
    vk
    csu
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
    csu
    #
    cA
    @2
    vj
    csu
    #
    cB
    @2
    vj
    csu
    #
    caddc
    co
    #
    cA
    cC
    vk
    csu
    #
    cB
    cC
    vk
    csu
    #
    caddc
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
    cbvsum
    a1i
    wph
    cA
    cB
    @2
    cU
    vj
    fsumsplitf.ab
    fsumsplitf.u
    fsumsplitf.fi
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
    fsumsplitf.ph
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
    fsumsplitf.c
    chvar
    fsumsplit
    @6
    @9
    wceq
    wph
    @4
    @7
    @5
    @8
    caddc
    @4
    @7
    @7
    cA
    @2
    cC
    vj
    vk
    @1
    @13
    wceq
    #
    @2
    vj
    @13
    @2
    csb
    #
    cC
    vj
    @13
    @2
    csbeq1a
    @22
    cC
    wceq
    @21
    @22
    vk
    @13
    cC
    csb
    cC
    vk
    vj
    @13
    cC
    csbco
    vk
    cC
    csbid
    eqtri
    a1i
    eqtrd
    #
    vk
    cA
    nfcv
    vj
    cA
    nfcv
    @12
    @11
    cbvsum
    @7
    eqid
    eqtri
    cB
    @2
    cC
    vj
    vk
    @12
    @11
    @23
    cbvsumi
    oveq12i
    a1i
    3eqtrd
end
