include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ello1mpt.mm"
include "mpbird.mm"

theorem ello1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  assume ello1mpt.1: |- ( ph -> A C_ RR )
  assume ello1mpt.2: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume ello1d.3: |- ( ph -> C e. RR )
  assume ello1d.4: |- ( ph -> M e. RR )
  assume ello1d.5: |- ( ( ph /\ ( x e. A /\ C <_ x ) ) -> B <_ M )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint M x
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint C m
  disjoint C y
  disjoint m ph
  disjoint ph y
  disjoint M m
  assert |- ( ph -> ( x e. A |-> B ) e. <_O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    clo1
    wcel
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    cB
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    vy
    cr
    wrex
    #
    wph
    cC
    cr
    wcel
    cM
    cr
    wcel
    cC
    @1
    cle
    wbr
    #
    cB
    cM
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    @7
    ello1d.3
    ello1d.4
    wph
    @10
    vx
    cA
    wph
    @1
    cA
    wcel
    @8
    @9
    ello1d.5
    expr
    ralrimiva
    @6
    @11
    @8
    @4
    wi
    #
    vx
    cA
    wral
    vy
    vm
    cC
    cM
    cr
    cr
    @0
    cC
    wceq
    #
    @5
    @12
    vx
    cA
    @13
    @2
    @8
    @4
    @0
    cC
    @1
    cle
    breq1
    imbi1d
    ralbidv
    @3
    cM
    wceq
    #
    @12
    @10
    vx
    cA
    @14
    @4
    @9
    @8
    @3
    cM
    cB
    cle
    breq2
    imbi2d
    ralbidv
    rspc2ev
    syl3anc
    wph
    vx
    vy
    cA
    cB
    vm
    ello1mpt.1
    ello1mpt.2
    ello1mpt
    mpbird
end
