include "csu.mm"
include "cv.mm"
include "csb.mm"
include "cc.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvsum.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
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
include "fsumcl.mm"
include "eqeltrd.mm"

theorem fsumclf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vj: setvar j
  assume fsumclf.ph: |- F/ k ph
  assume fsumclf.a: |- ( ph -> A e. Fin )
  assume fsumclf.b: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint j ph
  assert |- ( ph -> sum_ k e. A B e. CC )

  proof
    wph
    cA
    cB
    vk
    csu
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
    cc
    @0
    @3
    wceq
    wph
    cA
    cB
    @2
    vk
    vj
    vk
    @1
    cB
    csbeq1a
    #
    vj
    cA
    nfcv
    vk
    cA
    nfcv
    vj
    cB
    nfcv
    vk
    @1
    cB
    nfcsb1v
    #
    cbvsum
    a1i
    wph
    cA
    @2
    vj
    fsumclf.a
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
    @1
    cA
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
    @11
    @12
    vk
    wph
    @10
    vk
    fsumclf.ph
    @10
    vk
    nfv
    nfan
    vk
    @2
    cc
    @5
    nfel1
    nfim
    @6
    @1
    wceq
    #
    @8
    @11
    @9
    @12
    @13
    @7
    @10
    wph
    @6
    @1
    cA
    eleq1
    anbi2d
    @13
    cB
    @2
    cc
    @4
    eleq1d
    imbi12d
    fsumclf.b
    chvar
    fsumcl
    eqeltrd
end
