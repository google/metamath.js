include "cmpt.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wfn.mm"
include "wb.mm"
include "wcel.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "cbvmptv.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "wa.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "ralbidva.mm"
include "3bitrd.mm"

theorem fnmptfvd
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cU: class U
  let vi: setvar i
  let cM: class M
  let cV: class V
  let va: setvar a
  assume fnmptfvd.m: |- ( ph -> M Fn A )
  assume fnmptfvd.s: |- ( i = a -> D = C )
  assume fnmptfvd.d: |- ( ( ph /\ i e. A ) -> D e. U )
  assume fnmptfvd.c: |- ( ( ph /\ a e. A ) -> C e. V )

  disjoint A a
  disjoint A i
  disjoint a i
  disjoint C i
  disjoint D a
  disjoint M a
  disjoint M i
  disjoint U a
  disjoint U i
  disjoint V a
  disjoint V i
  disjoint a ph
  disjoint i ph
  assert |- ( ph -> ( M = ( a e. A |-> C ) <-> A. i e. A ( M ` i ) = D ) )

  proof
    wph
    cM
    va
    cA
    cC
    cmpt
    #
    wceq
    #
    vi
    cv
    #
    cM
    cfv
    #
    @2
    @0
    cfv
    #
    wceq
    #
    vi
    cA
    wral
    #
    @3
    @2
    vi
    cA
    cD
    cmpt
    #
    cfv
    #
    wceq
    #
    vi
    cA
    wral
    @3
    cD
    wceq
    #
    vi
    cA
    wral
    wph
    cM
    cA
    wfn
    @0
    cA
    wfn
    #
    @1
    @6
    wb
    fnmptfvd.m
    wph
    cC
    cV
    wcel
    #
    va
    cA
    wral
    @11
    wph
    @12
    va
    cA
    fnmptfvd.c
    ralrimiva
    va
    cA
    cC
    @0
    cV
    @0
    eqid
    fnmpt
    syl
    vi
    cA
    cM
    @0
    eqfnfv
    syl2anc
    wph
    @5
    @9
    vi
    cA
    wph
    @4
    @8
    @3
    wph
    @2
    @0
    @7
    @0
    @7
    wceq
    wph
    @7
    @0
    vi
    va
    cA
    cD
    cC
    fnmptfvd.s
    cbvmptv
    eqcomi
    a1i
    fveq1d
    eqeq2d
    ralbidv
    wph
    @9
    @10
    vi
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @8
    cD
    @3
    @14
    @13
    cD
    cU
    wcel
    @8
    cD
    wceq
    wph
    @13
    simpr
    fnmptfvd.d
    vi
    cA
    cD
    cU
    @7
    @7
    eqid
    fvmpt2
    syl2anc
    eqeq2d
    ralbidva
    3bitrd
end
