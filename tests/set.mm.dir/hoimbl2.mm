include "cico.mm"
include "co.mm"
include "cixp.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "csb.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nfcsb1.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "ixpeq2dva.mm"
include "nfov.mm"
include "cbvixp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "fmptdf.mm"
include "hoimbl.mm"
include "eqeltrd.mm"

theorem hoimbl2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  assume hoimbl2.k: |- F/ k ph
  assume hoimbl2.x: |- ( ph -> X e. Fin )
  assume hoimbl2.s: |- S = dom ( voln ` X )
  assume hoimbl2.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume hoimbl2.b: |- ( ( ph /\ k e. X ) -> B e. RR )

  disjoint X k
  disjoint A j
  disjoint B j
  disjoint S j
  disjoint X j
  disjoint j k
  disjoint j ph
  disjoint k x
  assert |- ( ph -> X_ k e. X ( A [,) B ) e. S )

  proof
    wph
    vk
    cX
    cA
    cB
    cico
    co
    #
    cixp
    #
    vj
    cX
    vj
    cv
    #
    vk
    cX
    cA
    cmpt
    #
    cfv
    #
    @2
    vk
    cX
    cB
    cmpt
    #
    cfv
    #
    cico
    co
    #
    cixp
    #
    cS
    wph
    @8
    vj
    cX
    vk
    @2
    cA
    csb
    #
    vk
    @2
    cB
    csb
    #
    cico
    co
    #
    cixp
    #
    @1
    wph
    vj
    cX
    @7
    @11
    wph
    @2
    cX
    wcel
    #
    wa
    #
    @4
    @9
    @6
    @10
    cico
    @14
    @13
    @9
    cr
    wcel
    #
    @4
    @9
    wceq
    wph
    @13
    simpr
    #
    wph
    vk
    cv
    #
    cX
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    #
    wi
    @14
    @15
    wi
    vk
    vj
    @14
    @15
    vk
    wph
    @13
    vk
    hoimbl2.k
    @13
    vk
    nfv
    nfan
    #
    vk
    @9
    cr
    vk
    @2
    cA
    nfcsb1v
    #
    vk
    cr
    nfcv
    #
    nfel
    nfim
    @17
    @2
    wceq
    #
    @19
    @14
    @20
    @15
    @24
    @18
    @13
    wph
    @17
    @2
    cX
    eleq1
    anbi2d
    #
    @24
    cA
    @9
    cr
    vk
    @2
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    hoimbl2.a
    chvar
    vk
    @2
    cA
    @9
    cX
    @3
    cr
    vk
    @2
    nfcv
    #
    vk
    @2
    cA
    @27
    nfcsb1
    @26
    @3
    eqid
    #
    fvmptf
    syl2anc
    @14
    @13
    @10
    cr
    wcel
    #
    @6
    @10
    wceq
    @16
    @19
    cB
    cr
    wcel
    #
    wi
    @14
    @29
    wi
    vk
    vj
    @14
    @29
    vk
    @21
    vk
    @10
    cr
    vk
    @2
    cB
    @27
    nfcsb1
    #
    @23
    nfel
    nfim
    @24
    @19
    @14
    @30
    @29
    @25
    @24
    cB
    @10
    cr
    vk
    @2
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    hoimbl2.b
    chvar
    vk
    @2
    cB
    @10
    cX
    @5
    cr
    @27
    @31
    @32
    @5
    eqid
    #
    fvmptf
    syl2anc
    oveq12d
    ixpeq2dva
    @12
    @1
    wceq
    wph
    @1
    @12
    vk
    vj
    cX
    @0
    @11
    vj
    @0
    nfcv
    vk
    @9
    @10
    cico
    @22
    vk
    cico
    nfcv
    @31
    nfov
    @24
    cA
    @9
    cB
    @10
    cico
    @26
    @32
    oveq12d
    cbvixp
    eqcomi
    a1i
    eqtr2d
    wph
    @3
    @5
    cS
    vj
    cX
    hoimbl2.x
    hoimbl2.s
    wph
    vk
    cX
    cA
    cr
    @3
    hoimbl2.k
    hoimbl2.a
    @28
    fmptdf
    wph
    vk
    cX
    cB
    cr
    @5
    hoimbl2.k
    hoimbl2.b
    @33
    fmptdf
    hoimbl
    eqeltrd
end
