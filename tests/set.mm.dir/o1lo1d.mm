include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "cneg.mm"
include "co1.mm"
include "wa.mm"
include "o1lo1.mm"
include "mpbid.mm"
include "simpld.mm"

theorem o1lo1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let cM: class M
  assume o1lo1.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume lo1o1.1: |- ( ph -> ( x e. A |-> B ) e. O(1) )

  disjoint A x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint M x
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> ( x e. A |-> B ) e. <_O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    clo1
    wcel
    #
    vx
    cA
    cB
    cneg
    cmpt
    clo1
    wcel
    #
    wph
    @0
    co1
    wcel
    @1
    @2
    wa
    lo1o1.1
    wph
    vx
    cA
    cB
    o1lo1.1
    o1lo1
    mpbid
    simpld
end
