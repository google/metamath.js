include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wf1.mm"
include "csn.mm"
include "cfv.mm"
include "cxp.mm"
include "ciun.mm"
include "cpw.mm"
include "wrex.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "unirnffid.mm"
include "wss.mm"
include "eqid.mm"
include "marypha2lem1.mm"
include "a1i.mm"
include "cima.mm"
include "cdom.mm"
include "wfn.mm"
include "wceq.mm"
include "cfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "marypha2lem4.mm"
include "sylan.mm"
include "breqtrrd.mm"
include "marypha1.mm"
include "df-rex.mm"
include "ssv.mm"
include "f1ss.mm"
include "mpan2.mm"
include "ad2antll.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "wb.mm"
include "adantr.mm"
include "f1fn.mm"
include "marypha2lem3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "syl5bi.mm"
include "mpd.mm"

theorem marypha2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let cF: class F
  let vd: setvar d
  assume marypha2.a: |- ( ph -> A e. Fin )
  assume marypha2.b: |- ( ph -> F : A --> Fin )
  assume marypha2.c: |- ( ( ph /\ d C_ A ) -> d ~<_ U. ( F " d ) )

  disjoint d ph
  disjoint g ph
  disjoint ph x
  disjoint d g
  disjoint d x
  disjoint g x
  disjoint A d
  disjoint A g
  disjoint A x
  disjoint F d
  disjoint F g
  disjoint F x
  assert |- ( ph -> E. g ( g : A -1-1-> _V /\ A. x e. A ( g ` x ) e. ( F ` x ) ) )

  proof
    wph
    cA
    cF
    crn
    cuni
    #
    vg
    cv
    #
    wf1
    #
    vg
    vx
    cA
    vx
    cv
    #
    csn
    @3
    cF
    cfv
    #
    cxp
    ciun
    #
    cpw
    #
    wrex
    #
    cA
    cvv
    @1
    wf1
    #
    @3
    @1
    cfv
    @4
    wcel
    vx
    cA
    wral
    #
    wa
    #
    vg
    wex
    #
    wph
    cA
    @0
    @5
    vg
    vd
    marypha2.a
    wph
    cA
    cF
    marypha2.b
    marypha2.a
    unirnffid
    @5
    cA
    @0
    cxp
    wss
    wph
    vx
    cA
    @5
    cF
    @5
    eqid
    #
    marypha2lem1
    a1i
    wph
    vd
    cv
    #
    cA
    wss
    #
    wa
    @13
    cF
    @13
    cima
    cuni
    #
    @5
    @13
    cima
    #
    cdom
    marypha2.c
    wph
    cF
    cA
    wfn
    #
    @14
    @16
    @15
    wceq
    wph
    cA
    cfn
    cF
    wf
    @17
    marypha2.b
    cA
    cfn
    cF
    ffn
    syl
    #
    vx
    cA
    @5
    cF
    @13
    @12
    marypha2lem4
    sylan
    breqtrrd
    marypha1
    @7
    @1
    @6
    wcel
    #
    @2
    wa
    #
    vg
    wex
    wph
    @11
    @2
    vg
    @6
    df-rex
    wph
    @20
    @10
    vg
    wph
    @20
    @10
    wph
    @20
    wa
    #
    @8
    @9
    @2
    @8
    wph
    @19
    @2
    @0
    cvv
    wss
    @8
    @0
    ssv
    cA
    @0
    cvv
    @1
    f1ss
    mpan2
    ad2antll
    @21
    @1
    @5
    wss
    #
    @9
    @19
    @22
    wph
    @2
    @1
    @5
    elpwi
    ad2antrl
    @21
    @17
    @1
    cA
    wfn
    #
    @22
    @9
    wb
    wph
    @17
    @20
    @18
    adantr
    @2
    @23
    wph
    @19
    cA
    @0
    @1
    f1fn
    ad2antll
    vx
    cA
    @5
    cF
    @1
    @12
    marypha2lem3
    syl2anc
    mpbid
    jca
    ex
    eximdv
    syl5bi
    mpd
end
