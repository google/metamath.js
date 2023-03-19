include "recnd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "adantrr.mm"
include "adantr.mm"
include "lesub2dd.mm"
include "abssuble0d.mm"
include "letrd.mm"
include "3brtr4d.mm"
include "rlimsqzlem.mm"

theorem rlimsqz
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  assume rlimsqz.d: |- ( ph -> D e. RR )
  assume rlimsqz.m: |- ( ph -> M e. RR )
  assume rlimsqz.l: |- ( ph -> ( x e. A |-> B ) ~~>r D )
  assume rlimsqz.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume rlimsqz.c: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume rlimsqz.1: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> B <_ C )
  assume rlimsqz.2: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> C <_ D )

  disjoint A x
  disjoint D x
  disjoint M x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> C ) ~~>r D )

  proof
    wph
    vx
    cA
    cB
    cC
    cD
    cD
    cM
    rlimsqz.m
    wph
    cD
    rlimsqz.d
    recnd
    rlimsqz.l
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    rlimsqz.b
    recnd
    @2
    cC
    rlimsqz.c
    recnd
    wph
    @1
    cM
    @0
    cle
    wbr
    #
    wa
    #
    wa
    #
    cD
    cC
    cmin
    co
    cD
    cB
    cmin
    co
    cC
    cD
    cmin
    co
    cabs
    cfv
    cB
    cD
    cmin
    co
    cabs
    cfv
    cle
    @5
    cB
    cC
    cD
    wph
    @1
    cB
    cr
    wcel
    @3
    rlimsqz.b
    adantrr
    #
    wph
    @1
    cC
    cr
    wcel
    @3
    rlimsqz.c
    adantrr
    #
    wph
    cD
    cr
    wcel
    @4
    rlimsqz.d
    adantr
    #
    rlimsqz.1
    lesub2dd
    @5
    cC
    cD
    @7
    @8
    rlimsqz.2
    abssuble0d
    @5
    cB
    cD
    @6
    @8
    @5
    cB
    cC
    cD
    @6
    @7
    @8
    rlimsqz.1
    rlimsqz.2
    letrd
    abssuble0d
    3brtr4d
    rlimsqzlem
end
