include "cv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "cmpt.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmbf.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "cr.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "breq12d.mm"
include "ifbieq12d.mm"
include "mpteq2dva.mm"
include "wf.mm"
include "0re.mm"
include "fconst6.mm"
include "a1i.mm"
include "cvol.mm"
include "cdm.mm"
include "cc.mm"
include "mbfdm2.mm"
include "0cnd.mm"
include "mbfconst.mm"
include "fmptd.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfif.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "mbfmax.mm"
include "eqeltrrd.mm"

theorem mbfpos
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mbfpos.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume mbfpos.2: |- ( ph -> ( x e. A |-> B ) e. MblFn )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> ( x e. A |-> if ( 0 <_ B , B , 0 ) ) e. MblFn )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cA
    cc0
    csn
    cxp
    #
    cfv
    #
    @0
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    cle
    wbr
    #
    @4
    @2
    cif
    #
    cmpt
    #
    vx
    cA
    cc0
    cB
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    cmpt
    cmbf
    wph
    vx
    cA
    @6
    @9
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @5
    @8
    @4
    @2
    cB
    cc0
    @11
    @2
    cc0
    @4
    cB
    cle
    @10
    @2
    cc0
    wceq
    wph
    cA
    cc0
    @0
    c0ex
    fvconst2
    adantl
    #
    @11
    @10
    cB
    cr
    wcel
    @4
    cB
    wceq
    wph
    @10
    simpr
    mbfpos.1
    vx
    cA
    cB
    cr
    @3
    @3
    eqid
    #
    fvmpt2
    syl2anc
    #
    breq12d
    @14
    @12
    ifbieq12d
    mpteq2dva
    wph
    vy
    cA
    @1
    @3
    @7
    cA
    cr
    @1
    wf
    wph
    cA
    cc0
    cr
    0re
    fconst6
    a1i
    wph
    cA
    cvol
    cdm
    wcel
    cc0
    cc
    wcel
    @1
    cmbf
    wcel
    wph
    vx
    cA
    cB
    cr
    mbfpos.2
    mbfpos.1
    mbfdm2
    wph
    0cnd
    cA
    cc0
    mbfconst
    syl2anc
    wph
    vx
    cA
    cB
    cr
    @3
    mbfpos.1
    @13
    fmptd
    mbfpos.2
    vx
    vy
    cA
    @6
    vy
    cv
    #
    @1
    cfv
    #
    @15
    @3
    cfv
    #
    cle
    wbr
    #
    @17
    @16
    cif
    vy
    @6
    nfcv
    @18
    vx
    @17
    @16
    vx
    @16
    @17
    cle
    vx
    @16
    nfcv
    #
    vx
    cle
    nfcv
    vx
    cA
    cB
    @15
    nffvmpt1
    #
    nfbr
    @20
    @19
    nfif
    @0
    @15
    wceq
    #
    @5
    @18
    @4
    @2
    @17
    @16
    @21
    @2
    @16
    @4
    @17
    cle
    @0
    @15
    @1
    fveq2
    #
    @0
    @15
    @3
    fveq2
    #
    breq12d
    @23
    @22
    ifbieq12d
    cbvmpt
    mbfmax
    eqeltrrd
end
