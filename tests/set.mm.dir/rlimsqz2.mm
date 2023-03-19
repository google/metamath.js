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
include "lesub1dd.mm"
include "abssubge0d.mm"
include "letrd.mm"
include "3brtr4d.mm"
include "rlimsqzlem.mm"

theorem rlimsqz2
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
  assume rlimsqz2.1: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> C <_ B )
  assume rlimsqz2.2: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> D <_ C )

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
    cC
    cD
    cmin
    co
    #
    cB
    cD
    cmin
    co
    #
    @6
    cabs
    cfv
    @7
    cabs
    cfv
    cle
    @5
    cC
    cB
    cD
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
    @1
    cB
    cr
    wcel
    @3
    rlimsqz.b
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
    rlimsqz2.1
    lesub1dd
    @5
    cD
    cC
    @10
    @8
    rlimsqz2.2
    abssubge0d
    @5
    cD
    cB
    @10
    @9
    @5
    cD
    cC
    cB
    @10
    @8
    @9
    rlimsqz2.2
    rlimsqz2.1
    letrd
    abssubge0d
    3brtr4d
    rlimsqzlem
end
