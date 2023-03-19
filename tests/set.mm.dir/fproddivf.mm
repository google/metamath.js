include "cdiv.mm"
include "co.mm"
include "cprod.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "oveq12d.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "cbvprod.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wi.mm"
include "nfvd.mm"
include "nfan1.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "cc0.mm"
include "wne.mm"
include "nfne.mm"
include "neeq1d.mm"
include "fproddiv.mm"
include "eqcomi.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "3eqtrd.mm"

theorem fproddivf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vj: setvar j
  assume fproddivf.kph: |- F/ k ph
  assume fproddivf.a: |- ( ph -> A e. Fin )
  assume fproddivf.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fproddivf.c: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume fproddivf.ne0: |- ( ( ph /\ k e. A ) -> C =/= 0 )

  disjoint A k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint j ph
  assert |- ( ph -> prod_ k e. A ( B / C ) = ( prod_ k e. A B / prod_ k e. A C ) )

  proof
    wph
    cA
    cB
    cC
    cdiv
    co
    #
    vk
    cprod
    #
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    vk
    @2
    cC
    csb
    #
    cdiv
    co
    #
    vj
    cprod
    #
    cA
    @3
    vj
    cprod
    #
    cA
    @4
    vj
    cprod
    #
    cdiv
    co
    cA
    cB
    vk
    cprod
    #
    cA
    cC
    vk
    cprod
    #
    cdiv
    co
    @1
    @6
    wceq
    wph
    cA
    @0
    @5
    vk
    vj
    vk
    cv
    #
    @2
    wceq
    #
    cB
    @3
    cC
    @4
    cdiv
    vk
    @2
    cB
    csbeq1a
    #
    vk
    @2
    cC
    csbeq1a
    #
    oveq12d
    vj
    cA
    nfcv
    #
    vk
    cA
    nfcv
    #
    vj
    @0
    nfcv
    vk
    @3
    @4
    cdiv
    vk
    @2
    cB
    nfcsb1v
    #
    vk
    cdiv
    nfcv
    vk
    @2
    cC
    nfcsb1v
    #
    nfov
    cbvprod
    a1i
    wph
    cA
    @3
    @4
    vj
    fproddivf.a
    wph
    @11
    cA
    wcel
    #
    wa
    #
    cB
    cc
    wcel
    #
    wi
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @3
    cc
    wcel
    #
    wi
    vk
    vj
    @23
    @24
    vk
    wph
    @22
    vk
    fproddivf.kph
    wph
    @22
    vk
    nfvd
    nfan1
    #
    vk
    @3
    cc
    @17
    vk
    cc
    nfcv
    #
    nfel
    nfim
    @12
    @20
    @23
    @21
    @24
    @12
    @19
    @22
    wph
    @11
    @2
    cA
    eleq1
    anbi2d
    #
    @12
    cB
    @3
    cc
    @13
    eleq1d
    imbi12d
    fproddivf.b
    chvar
    @20
    cC
    cc
    wcel
    #
    wi
    @23
    @4
    cc
    wcel
    #
    wi
    vk
    vj
    @23
    @29
    vk
    @25
    vk
    @4
    cc
    @18
    @26
    nfel
    nfim
    @12
    @20
    @23
    @28
    @29
    @27
    @12
    cC
    @4
    cc
    @14
    eleq1d
    imbi12d
    fproddivf.c
    chvar
    @20
    cC
    cc0
    wne
    #
    wi
    @23
    @4
    cc0
    wne
    #
    wi
    vk
    vj
    @23
    @31
    vk
    @25
    vk
    @4
    cc0
    @18
    vk
    cc0
    nfcv
    nfne
    nfim
    @12
    @20
    @23
    @30
    @31
    @27
    @12
    cC
    @4
    cc0
    @14
    neeq1d
    imbi12d
    fproddivf.ne0
    chvar
    fproddiv
    wph
    @7
    @9
    @8
    @10
    cdiv
    @7
    @9
    wceq
    wph
    @9
    @7
    cA
    cB
    @3
    vk
    vj
    @13
    @15
    @16
    vj
    cB
    nfcv
    @17
    cbvprod
    eqcomi
    a1i
    @8
    @10
    wceq
    wph
    cA
    @4
    cC
    vj
    vk
    @2
    @11
    wceq
    cC
    @4
    cC
    @4
    wceq
    vk
    vj
    @14
    equcoms
    eqcomd
    @16
    @15
    @18
    vj
    cC
    nfcv
    cbvprod
    a1i
    oveq12d
    3eqtrd
end
