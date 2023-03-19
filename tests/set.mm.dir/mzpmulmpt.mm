include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "mzpf.mm"
include "ffn.mm"
include "syl.mm"
include "cvv.mm"
include "ovex.mm"
include "ofmpteq.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "mzpmul.mm"
include "eqeltrrd.mm"

theorem mzpmulmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let cD: class D

  disjoint V x
  disjoint V a
  disjoint V b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint C x
  disjoint D x
  disjoint D a
  disjoint D b
  disjoint A a
  disjoint A b
  assert |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x e. ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) -> ( x e. ( ZZ ^m V ) |-> ( A x. B ) ) e. ( mzPoly ` V ) )

  proof
    vx
    cz
    cV
    cmap
    co
    #
    cA
    cmpt
    #
    cV
    cmzp
    cfv
    #
    wcel
    #
    vx
    @0
    cB
    cmpt
    #
    @2
    wcel
    #
    wa
    @1
    @4
    cmul
    cof
    co
    #
    vx
    @0
    cA
    cB
    cmul
    co
    cmpt
    #
    @2
    @3
    @1
    @0
    wfn
    #
    @4
    @0
    wfn
    #
    @6
    @7
    wceq
    #
    @5
    @3
    @0
    cz
    @1
    wf
    @8
    @1
    cV
    mzpf
    @0
    cz
    @1
    ffn
    syl
    @5
    @0
    cz
    @4
    wf
    @9
    @4
    cV
    mzpf
    @0
    cz
    @4
    ffn
    syl
    @0
    cvv
    wcel
    @8
    @9
    @10
    cz
    cV
    cmap
    ovex
    vx
    @0
    cA
    cB
    cmul
    cvv
    ofmpteq
    mp3an1
    syl2an
    @1
    @4
    cV
    mzpmul
    eqeltrrd
end
