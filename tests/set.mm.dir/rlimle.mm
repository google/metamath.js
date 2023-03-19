include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "rlimsub.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "resubcld.mm"
include "subge0d.mm"
include "mpbird.mm"
include "rlimge0.mm"
include "rlimrecl.mm"
include "mpbid.mm"

theorem rlimle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume rlimle.1: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimle.2: |- ( ph -> ( x e. A |-> B ) ~~>r D )
  assume rlimle.3: |- ( ph -> ( x e. A |-> C ) ~~>r E )
  assume rlimle.4: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume rlimle.5: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume rlimle.6: |- ( ( ph /\ x e. A ) -> B <_ C )

  disjoint A x
  disjoint D x
  disjoint ph x
  disjoint E x
  assert |- ( ph -> D <_ E )

  proof
    wph
    cc0
    cE
    cD
    cmin
    co
    #
    cle
    wbr
    cD
    cE
    cle
    wbr
    wph
    vx
    cA
    cC
    cB
    cmin
    co
    #
    @0
    rlimle.1
    wph
    vx
    cA
    cC
    cB
    cE
    cD
    cr
    rlimle.5
    rlimle.4
    rlimle.3
    rlimle.2
    rlimsub
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cC
    cB
    rlimle.5
    rlimle.4
    resubcld
    @2
    cc0
    @1
    cle
    wbr
    cB
    cC
    cle
    wbr
    rlimle.6
    @2
    cC
    cB
    rlimle.5
    rlimle.4
    subge0d
    mpbird
    rlimge0
    wph
    cE
    cD
    wph
    vx
    cA
    cC
    cE
    rlimle.1
    rlimle.3
    rlimle.5
    rlimrecl
    wph
    vx
    cA
    cB
    cD
    rlimle.1
    rlimle.2
    rlimle.4
    rlimrecl
    subge0d
    mpbid
end
