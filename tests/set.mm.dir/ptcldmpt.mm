include "cixp.mm"
include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "cpt.mm"
include "cfv.mm"
include "ccld.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvixp.mm"
include "ctop.mm"
include "eqid.mm"
include "fmptd.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfel.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "chvar.mm"
include "ptcld.mm"
include "syl5eqel.mm"

theorem ptcldmpt
  let wph: wff ph
  let cA: class A
  let cC: class C
  let vk: setvar k
  let cJ: class J
  let cV: class V
  let vl: setvar l
  assume ptcldmpt.a: |- ( ph -> A e. V )
  assume ptcldmpt.j: |- ( ( ph /\ k e. A ) -> J e. Top )
  assume ptcldmpt.c: |- ( ( ph /\ k e. A ) -> C e. ( Clsd ` J ) )

  disjoint k ph
  disjoint A k
  disjoint l ph
  disjoint k l
  disjoint A l
  disjoint C l
  disjoint J l
  disjoint V l
  assert |- ( ph -> X_ k e. A C e. ( Clsd ` ( Xt_ ` ( k e. A |-> J ) ) ) )

  proof
    wph
    vk
    cA
    cC
    cixp
    vl
    cA
    vk
    vl
    cv
    #
    cC
    csb
    #
    cixp
    vk
    cA
    cJ
    cmpt
    #
    cpt
    cfv
    ccld
    cfv
    vk
    vl
    cA
    cC
    @1
    vl
    cC
    nfcv
    vk
    @0
    cC
    nfcsb1v
    #
    vk
    @0
    cC
    csbeq1a
    #
    cbvixp
    wph
    cA
    @1
    vl
    @2
    cV
    ptcldmpt.a
    wph
    vk
    cA
    cJ
    ctop
    @2
    ptcldmpt.j
    @2
    eqid
    #
    fmptd
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cC
    @6
    @2
    cfv
    #
    ccld
    cfv
    #
    wcel
    #
    wi
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    @0
    @2
    cfv
    #
    ccld
    cfv
    #
    wcel
    #
    wi
    vk
    vl
    @13
    @16
    vk
    @13
    vk
    nfv
    vk
    @1
    @15
    @3
    vk
    @14
    ccld
    vk
    ccld
    nfcv
    vk
    cA
    cJ
    @0
    nffvmpt1
    nffv
    nfel
    nfim
    @6
    @0
    wceq
    #
    @8
    @13
    @11
    @16
    @17
    @7
    @12
    wph
    @6
    @0
    cA
    eleq1
    anbi2d
    @17
    cC
    @1
    @10
    @15
    @4
    @17
    @9
    @14
    ccld
    @6
    @0
    @2
    fveq2
    fveq2d
    eleq12d
    imbi12d
    @8
    cC
    cJ
    ccld
    cfv
    @10
    ptcldmpt.c
    @8
    @9
    cJ
    ccld
    @8
    @7
    cJ
    ctop
    wcel
    @9
    cJ
    wceq
    wph
    @7
    simpr
    ptcldmpt.j
    vk
    cA
    cJ
    ctop
    @2
    @5
    fvmpt2
    syl2anc
    fveq2d
    eleqtrrd
    chvar
    ptcld
    syl5eqel
end
