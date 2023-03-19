include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "wrex.mm"
include "cneg.mm"
include "cn.mm"
include "renegcl.mm"
include "arch.mm"
include "syl.mm"
include "wa.mm"
include "wb.mm"
include "nnre.mm"
include "ltnegcon1.mm"
include "ex.mm"
include "syl5.mm"
include "pm5.32d.mm"
include "nnnegz.mm"
include "breq1.mm"
include "rspcev.mm"
include "sylan.mm"
include "syl6bi.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "nnz.mm"
include "anim1i.mm"
include "reximi2.mm"
include "jca.mm"

theorem btwnz
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint A z
  assert |- ( A e. RR -> ( E. x e. ZZ x < A /\ E. y e. ZZ A < y ) )

  proof
    cA
    cr
    wcel
    #
    vx
    cv
    #
    cA
    clt
    wbr
    #
    vx
    cz
    wrex
    #
    cA
    vy
    cv
    #
    clt
    wbr
    #
    vy
    cz
    wrex
    #
    @0
    cA
    cneg
    #
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cn
    wrex
    #
    @3
    @0
    @7
    cr
    wcel
    @10
    cA
    renegcl
    @7
    vz
    arch
    syl
    @0
    @9
    @3
    vz
    cn
    @0
    @8
    cn
    wcel
    #
    @9
    @3
    @0
    @11
    @9
    wa
    @11
    @8
    cneg
    #
    cA
    clt
    wbr
    #
    wa
    @3
    @0
    @11
    @9
    @13
    @11
    @8
    cr
    wcel
    #
    @0
    @9
    @13
    wb
    #
    @8
    nnre
    @0
    @14
    @15
    cA
    @8
    ltnegcon1
    ex
    syl5
    pm5.32d
    @11
    @12
    cz
    wcel
    @13
    @3
    @8
    nnnegz
    @2
    @13
    vx
    @12
    cz
    @1
    @12
    cA
    clt
    breq1
    rspcev
    sylan
    syl6bi
    expd
    rexlimdv
    mpd
    @0
    @5
    vy
    cn
    wrex
    @6
    cA
    vy
    arch
    @5
    @5
    vy
    cn
    cz
    @4
    cn
    wcel
    @4
    cz
    wcel
    @5
    @4
    nnz
    anim1i
    reximi2
    syl
    jca
end
