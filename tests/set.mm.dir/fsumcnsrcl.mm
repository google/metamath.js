include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cnfldadd.mm"
include "subrgacl.mm"
include "3expb.mm"
include "sylan.mm"
include "csubg.mm"
include "cc0.mm"
include "subrgsubg.mm"
include "cnfld0.mm"
include "subg0cl.mm"
include "3syl.mm"
include "fsumcllem.mm"

theorem fsumcnsrcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  assume fsumcnsrcl.s: |- ( ph -> S e. ( SubRing ` CCfld ) )
  assume fsumcnsrcl.a: |- ( ph -> A e. Fin )
  assume fsumcnsrcl.b: |- ( ( ph /\ k e. A ) -> B e. S )

  disjoint k ph
  disjoint A k
  disjoint S k
  disjoint a ph
  disjoint b ph
  disjoint a k
  disjoint b k
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint S a
  disjoint S b
  assert |- ( ph -> sum_ k e. A B e. S )

  proof
    wph
    va
    vb
    cA
    cB
    cS
    vk
    wph
    cS
    ccnfld
    csubrg
    cfv
    wcel
    #
    cS
    cc
    wss
    fsumcnsrcl.s
    cS
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    wph
    @0
    va
    cv
    #
    cS
    wcel
    #
    vb
    cv
    #
    cS
    wcel
    #
    wa
    @1
    @3
    caddc
    co
    cS
    wcel
    #
    fsumcnsrcl.s
    @0
    @2
    @4
    @5
    cS
    caddc
    ccnfld
    @1
    @3
    cnfldadd
    subrgacl
    3expb
    sylan
    fsumcnsrcl.a
    fsumcnsrcl.b
    wph
    @0
    cS
    ccnfld
    csubg
    cfv
    wcel
    cc0
    cS
    wcel
    fsumcnsrcl.s
    cS
    ccnfld
    subrgsubg
    cS
    ccnfld
    cc0
    cnfld0
    subg0cl
    3syl
    fsumcllem
end
