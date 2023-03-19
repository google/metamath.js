include "cvoln.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cioo.mm"
include "co.mm"
include "cixp.mm"
include "cico.mm"
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
include "vonn0ioo.mm"
include "voliooico.mm"
include "prodeq2dv.mm"
include "nffv.mm"
include "cbvprod.mm"
include "3eqtrd.mm"

theorem vonn0ioo2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  assume vonn0ioo2.k: |- F/ k ph
  assume vonn0ioo2.x: |- ( ph -> X e. Fin )
  assume vonn0ioo2.n: |- ( ph -> X =/= (/) )
  assume vonn0ioo2.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume vonn0ioo2.b: |- ( ( ph /\ k e. X ) -> B e. RR )
  assume vonn0ioo2.i: |- I = X_ k e. X ( A (,) B )

  disjoint X k
  disjoint A j
  disjoint B j
  disjoint X j
  disjoint j k
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( ( voln ` X ) ` I ) = prod_ k e. X ( vol ` ( A (,) B ) ) )

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
    cioo
    co
    #
    cixp
    #
    @0
    cfv
    cX
    @3
    @5
    cico
    co
    #
    cvol
    cfv
    #
    vj
    cprod
    #
    cX
    cA
    cB
    cioo
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
    @11
    cixp
    #
    @7
    cI
    @14
    wceq
    wph
    vonn0ioo2.i
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
    cioo
    co
    #
    cixp
    #
    @14
    wph
    vj
    cX
    @6
    @17
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @3
    @15
    @5
    @16
    cioo
    @20
    @19
    @15
    cr
    wcel
    #
    @3
    @15
    wceq
    wph
    @19
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
    @20
    @21
    wi
    vk
    vj
    @20
    @21
    vk
    wph
    @19
    vk
    vonn0ioo2.k
    @19
    vk
    nfv
    nfan
    #
    vk
    @15
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
    @23
    @1
    wceq
    #
    @25
    @20
    @26
    @21
    @30
    @24
    @19
    wph
    @23
    @1
    cX
    eleq1
    anbi2d
    #
    @30
    cA
    @15
    cr
    vk
    @1
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    vonn0ioo2.a
    chvar
    #
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
    #
    @20
    @19
    @16
    cr
    wcel
    #
    @5
    @16
    wceq
    @22
    @25
    cB
    cr
    wcel
    #
    wi
    @20
    @36
    wi
    vk
    vj
    @20
    @36
    vk
    @27
    vk
    @16
    cr
    vk
    @1
    cB
    nfcsb1v
    #
    @29
    nfel
    nfim
    @30
    @25
    @20
    @37
    @36
    @31
    @30
    cB
    @16
    cr
    vk
    @1
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    vonn0ioo2.b
    chvar
    #
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
    #
    oveq12d
    ixpeq2dva
    @18
    @14
    wceq
    wph
    vj
    vk
    cX
    @17
    @11
    vk
    @15
    @16
    cioo
    @28
    vk
    cioo
    nfcv
    @38
    nfov
    #
    vj
    @11
    nfcv
    @1
    @23
    wceq
    #
    @15
    cA
    @16
    cB
    cioo
    @44
    @15
    cA
    cA
    @44
    cA
    @15
    cA
    @15
    wceq
    vk
    vj
    @32
    equcoms
    eqcomd
    @44
    cA
    eqidd
    eqtrd
    @44
    cB
    @16
    cB
    @16
    wceq
    vk
    vj
    @39
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
    vonn0ioo2.x
    vonn0ioo2.n
    wph
    vk
    cX
    cA
    cr
    @2
    vonn0ioo2.k
    vonn0ioo2.a
    @34
    fmptdf
    wph
    vk
    cX
    cB
    cr
    @4
    vonn0ioo2.k
    vonn0ioo2.b
    @41
    fmptdf
    @7
    eqid
    vonn0ioo
    wph
    @10
    cX
    @17
    cvol
    cfv
    #
    vj
    cprod
    #
    @13
    wph
    cX
    @9
    @46
    vj
    @20
    @9
    @15
    @16
    cico
    co
    #
    cvol
    cfv
    #
    @46
    @20
    @8
    @48
    cvol
    @20
    @3
    @15
    @5
    @16
    cico
    @35
    @42
    oveq12d
    fveq2d
    @20
    @46
    @49
    @20
    @15
    @16
    @33
    @40
    voliooico
    eqcomd
    eqtrd
    prodeq2dv
    @47
    @13
    wceq
    wph
    cX
    @46
    @12
    vj
    vk
    @44
    @17
    @11
    cvol
    @45
    fveq2d
    vk
    cX
    nfcv
    vj
    cX
    nfcv
    vk
    @17
    cvol
    vk
    cvol
    nfcv
    @43
    nffv
    vj
    @12
    nfcv
    cbvprod
    a1i
    eqtrd
    3eqtrd
end
