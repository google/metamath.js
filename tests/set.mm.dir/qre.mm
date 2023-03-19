include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "cr.mm"
include "elq.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "zre.mm"
include "nnre.mm"
include "nnne0.mm"
include "jca.mm"
include "redivcl.mm"
include "3expb.mm"
include "syl2an.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"

theorem qre
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. QQ -> A e. RR )

  proof
    cA
    cq
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    cA
    cr
    wcel
    #
    vx
    vy
    cA
    elq
    @3
    @4
    vx
    vy
    cz
    cn
    @0
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    @4
    @3
    @2
    cr
    wcel
    #
    @5
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @1
    cc0
    wne
    #
    wa
    @7
    @6
    @0
    zre
    @6
    @9
    @10
    @1
    nnre
    @1
    nnne0
    jca
    @8
    @9
    @10
    @7
    @0
    @1
    redivcl
    3expb
    syl2an
    cA
    @2
    cr
    eleq1
    syl5ibrcom
    rexlimivv
    sylbi
end
