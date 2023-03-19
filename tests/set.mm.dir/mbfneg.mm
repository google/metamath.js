include "c1.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmbf.mm"
include "cvv.mm"
include "cr.mm"
include "cdm.mm"
include "eqid.mm"
include "dmmptd.mm"
include "wcel.mm"
include "dmexg.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "cv.mm"
include "wa.mm"
include "neg1rr.mm"
include "a1i.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "offval2.mm"
include "mbfmptcl.mm"
include "mulm1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cc.mm"
include "fmptd.mm"
include "mbfmulc2re.mm"

theorem mbfneg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume mbfneg.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume mbfneg.2: |- ( ph -> ( x e. A |-> B ) e. MblFn )

  disjoint A x
  disjoint ph x
  disjoint V x
  assert |- ( ph -> ( x e. A |-> -u B ) e. MblFn )

  proof
    wph
    cA
    c1
    cneg
    #
    csn
    cxp
    #
    vx
    cA
    cB
    cmpt
    #
    cmul
    cof
    co
    #
    vx
    cA
    cB
    cneg
    #
    cmpt
    #
    cmbf
    wph
    @3
    vx
    cA
    @0
    cB
    cmul
    co
    #
    cmpt
    @5
    wph
    vx
    cA
    @0
    cB
    cmul
    @1
    @2
    cvv
    cr
    cV
    wph
    @2
    cdm
    #
    cA
    cvv
    wph
    vx
    @2
    cA
    cB
    cV
    @2
    eqid
    #
    mbfneg.1
    dmmptd
    wph
    @2
    cmbf
    wcel
    @7
    cvv
    wcel
    mbfneg.2
    @2
    cmbf
    dmexg
    syl
    eqeltrrd
    @0
    cr
    wcel
    #
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    neg1rr
    a1i
    mbfneg.1
    @1
    vx
    cA
    @0
    cmpt
    wceq
    wph
    vx
    cA
    @0
    fconstmpt
    a1i
    wph
    @2
    eqidd
    offval2
    wph
    vx
    cA
    @6
    @4
    @10
    cB
    wph
    vx
    cA
    cB
    cV
    mbfneg.2
    mbfneg.1
    mbfmptcl
    #
    mulm1d
    mpteq2dva
    eqtrd
    wph
    cA
    @0
    @2
    mbfneg.2
    @9
    wph
    neg1rr
    a1i
    wph
    vx
    cA
    cB
    cc
    @2
    @11
    @8
    fmptd
    mbfmulc2re
    eqeltrrd
end
