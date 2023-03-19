include "wrel.mm"
include "wf1.mm"
include "ccnv.mm"
include "ctpos.mm"
include "wa.mm"
include "cdm.mm"
include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "simpr.mm"
include "wf1o.mm"
include "relcnv.mm"
include "cnvf1o.mm"
include "f1of1.mm"
include "mp2b.mm"
include "wceq.mm"
include "wb.mm"
include "simpl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "f1eq3.mm"
include "syl.mm"
include "mpbii.mm"
include "f1dm.mm"
include "cnveqd.mm"
include "mpteq1.mm"
include "f1eq1.mm"
include "3syl.mm"
include "mpbird.mm"
include "f1co.mm"
include "syl2anc.mm"
include "releqd.mm"
include "biimparc.mm"
include "dftpos2.mm"
include "ex.mm"

theorem tposf12
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel A -> ( F : A -1-1-> B -> tpos F : `' A -1-1-> B ) )

  proof
    cA
    wrel
    #
    cA
    cB
    cF
    wf1
    #
    cA
    ccnv
    #
    cB
    cF
    ctpos
    #
    wf1
    #
    @0
    @1
    wa
    #
    @4
    @2
    cB
    cF
    vx
    cF
    cdm
    #
    ccnv
    #
    vx
    cv
    csn
    ccnv
    cuni
    #
    cmpt
    #
    ccom
    #
    wf1
    #
    @5
    @1
    @2
    cA
    @9
    wf1
    #
    @11
    @0
    @1
    simpr
    #
    @5
    @12
    @2
    cA
    vx
    @2
    @8
    cmpt
    #
    wf1
    #
    @5
    @2
    @2
    ccnv
    #
    @14
    wf1
    #
    @15
    @2
    wrel
    @2
    @16
    @14
    wf1o
    @17
    cA
    relcnv
    vx
    @2
    cnvf1o
    @2
    @16
    @14
    f1of1
    mp2b
    @5
    @16
    cA
    wceq
    #
    @17
    @15
    wb
    @5
    @0
    @18
    @0
    @1
    simpl
    cA
    dfrel2
    sylib
    @16
    cA
    @2
    @14
    f1eq3
    syl
    mpbii
    @5
    @7
    @2
    wceq
    @9
    @14
    wceq
    @12
    @15
    wb
    @5
    @6
    cA
    @5
    @1
    @6
    cA
    wceq
    @13
    cA
    cB
    cF
    f1dm
    #
    syl
    cnveqd
    vx
    @7
    @2
    @8
    mpteq1
    @2
    cA
    @9
    @14
    f1eq1
    3syl
    mpbird
    @2
    cA
    cB
    cF
    @9
    f1co
    syl2anc
    @5
    @6
    wrel
    #
    @3
    @10
    wceq
    @4
    @11
    wb
    @1
    @20
    @0
    @1
    @6
    cA
    @19
    releqd
    biimparc
    vx
    cF
    dftpos2
    @2
    cB
    @3
    @10
    f1eq1
    3syl
    mpbird
    ex
end
