include "citg.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "csb.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "df-itg.mm"
include "wceq.mm"
include "fvex.mm"
include "id.mm"
include "syl6eqr.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "ifbieq1d.mm"
include "csbie.mm"
include "mpteq2i.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "a1i.mm"
include "sumeq2i.mm"
include "eqtri.mm"

theorem dfitg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vk: setvar k
  let vy: setvar y
  assume dfitg.1: |- T = ( Re ` ( B / ( _i ^ k ) ) )

  disjoint k x
  disjoint A k
  disjoint B k
  disjoint k y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint T y
  assert |- S. A B _d x = sum_ k e. ( 0 ... 3 ) ( ( _i ^ k ) x. ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ T ) , T , 0 ) ) ) )

  proof
    vx
    cA
    cB
    citg
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cr
    vy
    cB
    @2
    cdiv
    co
    #
    cre
    cfv
    #
    vx
    cv
    cA
    wcel
    #
    cc0
    vy
    cv
    #
    cle
    wbr
    #
    wa
    #
    @6
    cc0
    cif
    #
    csb
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    @0
    @2
    vx
    cr
    @5
    cc0
    cT
    cle
    wbr
    #
    wa
    #
    cT
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    vx
    vy
    cA
    cB
    vk
    df-itg
    @0
    @13
    @19
    vk
    @13
    @19
    wceq
    @1
    @0
    wcel
    @12
    @18
    @2
    cmul
    @11
    @17
    citg2
    vx
    cr
    @10
    @16
    vy
    @4
    @9
    @16
    @3
    cre
    fvex
    @6
    @4
    wceq
    #
    @8
    @15
    @6
    cT
    cc0
    @20
    @7
    @14
    @5
    @20
    @6
    cT
    cc0
    cle
    @20
    @6
    @4
    cT
    @20
    id
    dfitg.1
    syl6eqr
    #
    breq2d
    anbi2d
    @21
    ifbieq1d
    csbie
    mpteq2i
    fveq2i
    oveq2i
    a1i
    sumeq2i
    eqtri
end
