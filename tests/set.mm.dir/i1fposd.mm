include "cr.mm"
include "cc0.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "citg1.mm"
include "cdm.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfif.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wf.mm"
include "wral.mm"
include "i1ff.mm"
include "syl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "i1fpos.mm"
include "eqeltrrd.mm"

theorem i1fposd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume i1fposd.1: |- ( ph -> ( x e. RR |-> A ) e. dom S.1 )

  disjoint ph x
  disjoint x y
  disjoint ph y
  disjoint A y
  assert |- ( ph -> ( x e. RR |-> if ( 0 <_ A , A , 0 ) ) e. dom S.1 )

  proof
    wph
    vy
    cr
    cc0
    vy
    cv
    #
    vx
    cr
    cA
    cmpt
    #
    cfv
    #
    cle
    wbr
    #
    @2
    cc0
    cif
    #
    cmpt
    #
    vx
    cr
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    citg1
    cdm
    #
    wph
    @5
    vx
    cr
    cc0
    vx
    cv
    #
    @1
    cfv
    #
    cle
    wbr
    #
    @11
    cc0
    cif
    #
    cmpt
    @8
    vy
    vx
    cr
    @4
    @13
    @3
    vx
    @2
    cc0
    vx
    cc0
    @2
    cle
    vx
    cc0
    nfcv
    #
    vx
    cle
    nfcv
    vx
    cr
    cA
    @0
    nffvmpt1
    #
    nfbr
    @15
    @14
    nfif
    vy
    @13
    nfcv
    @0
    @10
    wceq
    #
    @3
    @12
    @2
    @11
    cc0
    @16
    @2
    @11
    cc0
    cle
    @0
    @10
    @1
    fveq2
    #
    breq2d
    @17
    ifbieq1d
    cbvmpt
    wph
    vx
    cr
    @13
    @7
    wph
    @10
    cr
    wcel
    #
    wa
    #
    @12
    @6
    @11
    cA
    cc0
    @19
    @11
    cA
    cc0
    cle
    @19
    @18
    cA
    cr
    wcel
    #
    @11
    cA
    wceq
    wph
    @18
    simpr
    wph
    @20
    vx
    cr
    wph
    cr
    cr
    @1
    wf
    #
    @20
    vx
    cr
    wral
    wph
    @1
    @9
    wcel
    #
    @21
    i1fposd.1
    @1
    i1ff
    syl
    vx
    cr
    cr
    cA
    @1
    @1
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    vx
    cr
    cA
    cr
    @1
    @23
    fvmpt2
    syl2anc
    #
    breq2d
    @24
    ifbieq1d
    mpteq2dva
    syl5eq
    wph
    @22
    @5
    @9
    wcel
    i1fposd.1
    vy
    @1
    @5
    @5
    eqid
    i1fpos
    syl
    eqeltrrd
end
