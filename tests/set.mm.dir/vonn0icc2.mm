include "cvoln.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cicc.mm"
include "co.mm"
include "cixp.mm"
include "cvol.mm"
include "cprod.mm"
include "wceq.mm"
include "a1i.mm"
include "csb.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
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
include "eqid.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "ixpeq2dva.mm"
include "nfov.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "eqtrd.mm"
include "cbvixp.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "fmptdf.mm"
include "vonn0icc.mm"
include "prodeq2dv.mm"
include "nffv.mm"
include "cbvprod.mm"
include "3eqtrd.mm"

theorem vonn0icc2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  assume vonn0icc2.k: |- F/ k ph
  assume vonn0icc2.x: |- ( ph -> X e. Fin )
  assume vonn0icc2.n: |- ( ph -> X =/= (/) )
  assume vonn0icc2.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume vonn0icc2.b: |- ( ( ph /\ k e. X ) -> B e. RR )
  assume vonn0icc2.i: |- I = X_ k e. X ( A [,] B )

  disjoint X k
  disjoint A j
  disjoint B j
  disjoint X j
  disjoint j k
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( ( voln ` X ) ` I ) = prod_ k e. X ( vol ` ( A [,] B ) ) )

  proof
    wph
    cI
    cX
    cvoln
    cfv
    #
    cfv
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
    @1
    vk
    cX
    cB
    cmpt
    #
    cfv
    #
    cicc
    co
    #
    cixp
    #
    @0
    cfv
    cX
    @6
    cvol
    cfv
    #
    vj
    cprod
    #
    cX
    cA
    cB
    cicc
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    wph
    cI
    @7
    @0
    wph
    cI
    vk
    cX
    @10
    cixp
    #
    @7
    cI
    @13
    wceq
    wph
    vonn0icc2.i
    a1i
    wph
    @7
    vj
    cX
    vk
    @1
    cA
    csb
    #
    vk
    @1
    cB
    csb
    #
    cicc
    co
    #
    cixp
    #
    @13
    wph
    vj
    cX
    @6
    @16
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @3
    @14
    @5
    @15
    cicc
    @19
    @18
    @14
    cr
    wcel
    #
    @3
    @14
    wceq
    wph
    @18
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
    @19
    @20
    wi
    vk
    vj
    @19
    @20
    vk
    wph
    @18
    vk
    vonn0icc2.k
    @18
    vk
    nfv
    nfan
    #
    vk
    @14
    cr
    vk
    @1
    cA
    nfcsb1v
    #
    vk
    cr
    nfcv
    #
    nfel
    nfim
    @22
    @1
    wceq
    #
    @24
    @19
    @25
    @20
    @29
    @23
    @18
    wph
    @22
    @1
    cX
    eleq1
    anbi2d
    #
    @29
    cA
    @14
    cr
    vk
    @1
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    vonn0icc2.a
    chvar
    vk
    @1
    cA
    cX
    @2
    cr
    @2
    eqid
    #
    fvmpts
    syl2anc
    @19
    @18
    @15
    cr
    wcel
    #
    @5
    @15
    wceq
    @21
    @24
    cB
    cr
    wcel
    #
    wi
    @19
    @33
    wi
    vk
    vj
    @19
    @33
    vk
    @26
    vk
    @15
    cr
    vk
    @1
    cB
    nfcsb1v
    #
    @28
    nfel
    nfim
    @29
    @24
    @19
    @34
    @33
    @30
    @29
    cB
    @15
    cr
    vk
    @1
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    vonn0icc2.b
    chvar
    vk
    @1
    cB
    cX
    @4
    cr
    @4
    eqid
    #
    fvmpts
    syl2anc
    oveq12d
    #
    ixpeq2dva
    @17
    @13
    wceq
    wph
    vj
    vk
    cX
    @16
    @10
    vk
    @14
    @15
    cicc
    @27
    vk
    cicc
    nfcv
    @35
    nfov
    #
    vj
    @10
    nfcv
    @1
    @22
    wceq
    #
    @14
    cA
    @15
    cB
    cicc
    @40
    @14
    cA
    cA
    @40
    cA
    @14
    cA
    @14
    wceq
    vk
    vj
    @31
    equcoms
    eqcomd
    @40
    cA
    eqidd
    eqtrd
    @40
    cB
    @15
    cB
    @15
    wceq
    vk
    vj
    @36
    equcoms
    eqcomd
    oveq12d
    #
    cbvixp
    a1i
    eqtrd
    eqtr4d
    fveq2d
    wph
    @2
    @4
    vj
    @7
    cX
    vonn0icc2.x
    vonn0icc2.n
    wph
    vk
    cX
    cA
    cr
    @2
    vonn0icc2.k
    vonn0icc2.a
    @32
    fmptdf
    wph
    vk
    cX
    cB
    cr
    @4
    vonn0icc2.k
    vonn0icc2.b
    @37
    fmptdf
    @7
    eqid
    vonn0icc
    wph
    @9
    cX
    @16
    cvol
    cfv
    #
    vj
    cprod
    #
    @12
    wph
    cX
    @8
    @42
    vj
    @19
    @6
    @16
    cvol
    @38
    fveq2d
    prodeq2dv
    @43
    @12
    wceq
    wph
    cX
    @42
    @11
    vj
    vk
    @40
    @16
    @10
    cvol
    @41
    fveq2d
    vk
    cX
    nfcv
    vj
    cX
    nfcv
    vk
    @16
    cvol
    vk
    cvol
    nfcv
    @39
    nffv
    vj
    @11
    nfcv
    cbvprod
    a1i
    eqtrd
    3eqtrd
end
