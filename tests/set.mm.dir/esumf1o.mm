include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cesum.mm"
include "ccom.mm"
include "xrge0base.mm"
include "ccmn.mm"
include "wcel.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctps.mm"
include "xrge0tps.mm"
include "eqid.mm"
include "fmptd.mm"
include "tsmsf1o.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "feqmptdf.mm"
include "mpteq2da.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "fmptcof2.mm"
include "oveq2d.mm"
include "unieqd.mm"
include "df-esum.mm"
include "3eqtr4g.mm"

theorem esumf1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cV: class V
  assume esumf1o.0: |- F/ n ph
  assume esumf1o.b: |- F/_ n B
  assume esumf1o.d: |- F/_ k D
  assume esumf1o.a: |- F/_ n A
  assume esumf1o.c: |- F/_ n C
  assume esumf1o.f: |- F/_ n F
  assume esumf1o.1: |- ( k = G -> B = D )
  assume esumf1o.2: |- ( ph -> A e. V )
  assume esumf1o.3: |- ( ph -> F : C -1-1-onto-> A )
  assume esumf1o.4: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume esumf1o.5: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint k n
  disjoint A k
  disjoint C k
  disjoint G k
  disjoint k ph
  assert |- ( ph -> sum* k e. A B = sum* n e. C D )

  proof
    wph
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    cuni
    @1
    vn
    cC
    cD
    cmpt
    #
    ctsu
    co
    #
    cuni
    cA
    cB
    vk
    cesum
    cC
    cD
    vn
    cesum
    wph
    @3
    @5
    wph
    @3
    @1
    @2
    cF
    ccom
    #
    ctsu
    co
    @5
    wph
    cA
    @0
    cC
    @2
    @1
    cF
    cV
    xrge0base
    @1
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @1
    ctps
    wcel
    wph
    xrge0tps
    a1i
    esumf1o.2
    wph
    vk
    cA
    cB
    @0
    @2
    esumf1o.5
    @2
    eqid
    fmptd
    esumf1o.3
    tsmsf1o
    wph
    @6
    @4
    @1
    ctsu
    wph
    vn
    vk
    cC
    cA
    cG
    cB
    cD
    cF
    @2
    esumf1o.b
    esumf1o.d
    esumf1o.c
    esumf1o.a
    esumf1o.0
    wph
    cG
    cA
    wcel
    #
    vn
    cC
    esumf1o.0
    wph
    vn
    cv
    #
    cC
    wcel
    #
    @7
    wph
    @9
    wa
    @8
    cF
    cfv
    #
    cG
    cA
    esumf1o.4
    wph
    cC
    cA
    @8
    cF
    wph
    cC
    cA
    cF
    wf1o
    cC
    cA
    cF
    wf
    esumf1o.3
    cC
    cA
    cF
    f1of
    syl
    #
    ffvelrnda
    eqeltrrd
    ex
    ralrimi
    wph
    cF
    vn
    cC
    @10
    cmpt
    vn
    cC
    cG
    cmpt
    wph
    vn
    cC
    cA
    cF
    esumf1o.c
    esumf1o.f
    @11
    feqmptdf
    wph
    vn
    cC
    @10
    cG
    esumf1o.0
    esumf1o.4
    mpteq2da
    eqtrd
    wph
    @2
    eqidd
    esumf1o.1
    fmptcof2
    oveq2d
    eqtrd
    unieqd
    cA
    cB
    vk
    df-esum
    cC
    cD
    vn
    df-esum
    3eqtr4g
end
