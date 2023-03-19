include "cv.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "oveq2.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "ifbieq1d.mm"
include "mpteq2dv.mm"

theorem itgvallem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vk: setvar k
  let cK: class K
  assume itgvallem.1: |- ( _i ^ K ) = T

  disjoint k x
  disjoint K x
  assert |- ( k = K -> ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Re ` ( B / ( _i ^ k ) ) ) ) , ( Re ` ( B / ( _i ^ k ) ) ) , 0 ) ) ) = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Re ` ( B / T ) ) ) , ( Re ` ( B / T ) ) , 0 ) ) ) )

  proof
    vk
    cv
    #
    cK
    wceq
    #
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    ci
    @0
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @5
    cc0
    cif
    #
    cmpt
    vx
    cr
    @2
    cc0
    cB
    cT
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @10
    cc0
    cif
    #
    cmpt
    citg2
    @1
    vx
    cr
    @8
    @13
    @1
    @7
    @12
    @5
    @10
    cc0
    @1
    @6
    @11
    @2
    @1
    @5
    @10
    cc0
    cle
    @1
    @4
    @9
    cre
    @1
    @3
    cT
    cB
    cdiv
    @1
    @3
    ci
    cK
    cexp
    co
    cT
    @0
    cK
    ci
    cexp
    oveq2
    itgvallem.1
    syl6eq
    oveq2d
    fveq2d
    #
    breq2d
    anbi2d
    @14
    ifbieq1d
    mpteq2dv
    fveq2d
end
