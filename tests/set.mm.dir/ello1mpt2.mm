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
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "ello1mpt.mm"
include "wss.mm"
include "wb.mm"
include "rexico.mm"
include "syl2anc.mm"
include "rexbidv.mm"
include "rexcom.mm"
include "3bitr4g.mm"
include "bitr4d.mm"

theorem ello1mpt2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vz: setvar z
  let cM: class M
  assume ello1mpt.1: |- ( ph -> A C_ RR )
  assume ello1mpt.2: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume ello1d.3: |- ( ph -> C e. RR )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint m z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint M m
  disjoint M x
  assert |- ( ph -> ( ( x e. A |-> B ) e. <_O(1) <-> E. y e. ( C [,) +oo ) E. m e. RR A. x e. A ( y <_ x -> B <_ m ) ) )

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
    vx
    cv
    cle
    wbr
    cB
    vm
    cv
    cle
    wbr
    #
    wi
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    @2
    vy
    cC
    cpnf
    cico
    co
    #
    wrex
    #
    wph
    vx
    vy
    cA
    cB
    vm
    ello1mpt.1
    ello1mpt.2
    ello1mpt
    wph
    @1
    vy
    @4
    wrex
    #
    vm
    cr
    wrex
    @1
    vy
    cr
    wrex
    #
    vm
    cr
    wrex
    @5
    @3
    wph
    @6
    @7
    vm
    cr
    wph
    cA
    cr
    wss
    cC
    cr
    wcel
    @6
    @7
    wb
    ello1mpt.1
    ello1d.3
    @0
    cA
    cC
    vy
    vx
    rexico
    syl2anc
    rexbidv
    @1
    vy
    vm
    @4
    cr
    rexcom
    @1
    vy
    vm
    cr
    cr
    rexcom
    3bitr4g
    bitr4d
end
