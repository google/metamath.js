include "cprod.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wnfc.mm"
include "a1i.mm"
include "cv.mm"
include "wceq.mm"
include "adantl.mm"
include "fprodsplit1f.mm"
include "oveq1d.mm"
include "cfn.mm"
include "wcel.mm"
include "diffi.mm"
include "syl.mm"
include "wa.mm"
include "cc.mm"
include "simpl.mm"
include "eldifi.mm"
include "syl2anc.mm"
include "fprodclf.mm"
include "mul02d.mm"
include "3eqtrd.mm"

theorem fprod0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cK: class K
  assume fprod0.kph: |- F/ k ph
  assume fprod0.kc: |- F/_ k C
  assume fprod0.a: |- ( ph -> A e. Fin )
  assume fprod0.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprod0.bc: |- ( k = K -> B = C )
  assume fprod0.k: |- ( ph -> K e. A )
  assume fprod0.c: |- ( ph -> C = 0 )

  disjoint A k
  disjoint K k
  assert |- ( ph -> prod_ k e. A B = 0 )

  proof
    wph
    cA
    cB
    vk
    cprod
    cC
    cA
    cK
    csn
    #
    cdif
    #
    cB
    vk
    cprod
    #
    cmul
    co
    cc0
    @2
    cmul
    co
    cc0
    wph
    cA
    cB
    cK
    cC
    vk
    fprod0.kph
    vk
    cC
    wnfc
    wph
    fprod0.kc
    a1i
    fprod0.a
    fprod0.b
    fprod0.k
    vk
    cv
    #
    cK
    wceq
    cB
    cC
    wceq
    wph
    fprod0.bc
    adantl
    fprodsplit1f
    wph
    cC
    cc0
    @2
    cmul
    fprod0.c
    oveq1d
    wph
    @2
    wph
    @1
    cB
    vk
    fprod0.kph
    wph
    cA
    cfn
    wcel
    @1
    cfn
    wcel
    fprod0.a
    cA
    @0
    diffi
    syl
    wph
    @3
    @1
    wcel
    #
    wa
    wph
    @3
    cA
    wcel
    #
    cB
    cc
    wcel
    wph
    @4
    simpl
    @4
    @5
    wph
    @3
    cA
    @0
    eldifi
    adantl
    fprod0.b
    syl2anc
    fprodclf
    mul02d
    3eqtrd
end
