include "cmpt2.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wfn.mm"
include "wb.mm"
include "wcel.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fnmpt2.mm"
include "syl.mm"
include "eqfnov2.mm"
include "syl2anc.mm"
include "nfcv.mm"
include "cbvmpt2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "2ralbidva.mm"
include "3bitrd.mm"

theorem fnmpt2ovd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume fnmpt2ovd.m: |- ( ph -> M Fn ( A X. B ) )
  assume fnmpt2ovd.s: |- ( ( i = a /\ j = b ) -> D = C )
  assume fnmpt2ovd.d: |- ( ( ph /\ i e. A /\ j e. B ) -> D e. U )
  assume fnmpt2ovd.c: |- ( ( ph /\ a e. A /\ b e. B ) -> C e. V )
  assume fnmpt2ovd.v: |- ( ph -> ( A e. X /\ B e. Y ) )

  disjoint A a
  disjoint A b
  disjoint A i
  disjoint A j
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i j
  disjoint B a
  disjoint B b
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint D a
  disjoint D b
  disjoint M a
  disjoint M b
  disjoint M i
  disjoint M j
  disjoint U a
  disjoint U b
  disjoint U i
  disjoint U j
  disjoint V a
  disjoint V b
  disjoint V i
  disjoint V j
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint Y a
  disjoint Y b
  disjoint Y i
  disjoint Y j
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> ( M = ( a e. A , b e. B |-> C ) <-> A. i e. A A. j e. B ( i M j ) = D ) )

  proof
    wph
    cM
    va
    vb
    cA
    cB
    cC
    cmpt2
    #
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    @2
    @3
    @0
    co
    #
    wceq
    #
    vj
    cB
    wral
    vi
    cA
    wral
    #
    @4
    @2
    @3
    vi
    vj
    cA
    cB
    cD
    cmpt2
    #
    co
    #
    wceq
    #
    vj
    cB
    wral
    vi
    cA
    wral
    @4
    cD
    wceq
    #
    vj
    cB
    wral
    vi
    cA
    wral
    wph
    cM
    cA
    cB
    cxp
    #
    wfn
    @0
    @12
    wfn
    #
    @1
    @7
    wb
    fnmpt2ovd.m
    wph
    cC
    cV
    wcel
    #
    vb
    cB
    wral
    va
    cA
    wral
    @13
    wph
    @14
    va
    vb
    cA
    cB
    wph
    va
    cv
    cA
    wcel
    vb
    cv
    cB
    wcel
    @14
    fnmpt2ovd.c
    3expb
    ralrimivva
    va
    vb
    cA
    cB
    cC
    @0
    cV
    @0
    eqid
    fnmpt2
    syl
    vi
    vj
    cA
    cB
    cM
    @0
    eqfnov2
    syl2anc
    wph
    @6
    @10
    vi
    vj
    cA
    cB
    wph
    @5
    @9
    @4
    wph
    @0
    @8
    @2
    @3
    @0
    @8
    wceq
    wph
    @8
    @0
    vi
    vj
    va
    vb
    cA
    cB
    cD
    cC
    va
    cD
    nfcv
    vb
    cD
    nfcv
    vi
    cC
    nfcv
    vj
    cC
    nfcv
    fnmpt2ovd.s
    cbvmpt2
    eqcomi
    a1i
    oveqd
    eqeq2d
    2ralbidv
    wph
    @10
    @11
    vi
    vj
    cA
    cB
    wph
    @2
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    wa
    #
    @9
    cD
    @4
    @17
    @15
    @16
    cD
    cU
    wcel
    #
    @9
    cD
    wceq
    wph
    @15
    @16
    simprl
    wph
    @15
    @16
    simprr
    wph
    @15
    @16
    @18
    fnmpt2ovd.d
    3expb
    vi
    vj
    cA
    cB
    cD
    @8
    cU
    @8
    eqid
    ovmpt4g
    syl3anc
    eqeq2d
    2ralbidva
    3bitrd
end
