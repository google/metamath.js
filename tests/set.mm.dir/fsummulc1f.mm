include "csu.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvsum.mm"
include "oveq1i.mm"
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
include "fsummulc1.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "oveq1d.mm"
include "nfov.mm"
include "3eqtrd.mm"

theorem fsummulc1f
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vj: setvar j
  assume fsummulc1f.ph: |- F/ k ph
  assume fsummulclf.a: |- ( ph -> A e. Fin )
  assume fsummulclf.c: |- ( ph -> C e. CC )
  assume fsummulclf.b: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint C k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint j ph
  assert |- ( ph -> ( sum_ k e. A B x. C ) = sum_ k e. A ( B x. C ) )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cC
    cmul
    co
    #
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    vj
    csu
    #
    cC
    cmul
    co
    #
    cA
    @3
    cC
    cmul
    co
    #
    vj
    csu
    #
    cA
    cB
    cC
    cmul
    co
    #
    vk
    csu
    #
    @1
    @5
    wceq
    wph
    @0
    @4
    cC
    cmul
    cA
    cB
    @3
    vk
    vj
    vk
    @2
    cB
    csbeq1a
    #
    vj
    cA
    nfcv
    #
    vk
    cA
    nfcv
    #
    vj
    cB
    nfcv
    vk
    @2
    cB
    nfcsb1v
    #
    cbvsum
    oveq1i
    a1i
    wph
    cA
    @3
    cC
    vj
    fsummulclf.a
    fsummulclf.c
    wph
    vk
    cv
    #
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
    @19
    @20
    vk
    wph
    @18
    vk
    fsummulc1f.ph
    @18
    vk
    nfv
    nfan
    vk
    @3
    cc
    @13
    nfel1
    nfim
    @14
    @2
    wceq
    #
    @16
    @19
    @17
    @20
    @21
    @15
    @18
    wph
    @14
    @2
    cA
    eleq1
    anbi2d
    @21
    cB
    @3
    cc
    @10
    eleq1d
    imbi12d
    fsummulclf.b
    chvar
    fsummulc1
    @7
    @9
    wceq
    wph
    cA
    @6
    @8
    vj
    vk
    @2
    @14
    wceq
    #
    @3
    cB
    cC
    cmul
    @21
    cB
    @3
    wceq
    #
    wi
    #
    @22
    @3
    cB
    wceq
    #
    wi
    #
    @10
    @24
    @22
    @23
    wi
    @26
    @21
    @22
    @23
    @14
    @2
    eqcom
    imbi1i
    @23
    @25
    @22
    cB
    @3
    eqcom
    imbi2i
    bitri
    mpbi
    oveq1d
    @12
    @11
    vk
    @3
    cC
    cmul
    @13
    vk
    cmul
    nfcv
    vk
    cC
    nfcv
    nfov
    vj
    @8
    nfcv
    cbvsum
    a1i
    3eqtrd
end
