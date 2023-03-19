include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "clt.mm"
include "arch.mm"
include "nnre.mm"
include "w3a.mm"
include "lelttr.mm"
include "ltle.mm"
include "3adant2.mm"
include "syld.mm"
include "exp5o.mm"
include "com3l.mm"
include "imp4b.mm"
include "com23.mm"
include "sylan2.mm"
include "reximdva.mm"
include "mpd.mm"
include "r19.35.mm"
include "sylib.mm"
include "rexlimiv.mm"

theorem bndndx
  let vx: setvar x
  let cA: class A
  let vk: setvar k

  disjoint A x
  disjoint k x
  assert |- ( E. x e. RR A. k e. NN ( A e. RR /\ A <_ x ) -> E. k e. NN A <_ k )

  proof
    cA
    cr
    wcel
    #
    cA
    vx
    cv
    #
    cle
    wbr
    #
    wa
    #
    vk
    cn
    wral
    #
    cA
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cn
    wrex
    #
    vx
    cr
    @1
    cr
    wcel
    #
    @3
    @6
    wi
    #
    vk
    cn
    wrex
    #
    @4
    @7
    wi
    @8
    @1
    @5
    clt
    wbr
    #
    vk
    cn
    wrex
    @10
    @1
    vk
    arch
    @8
    @11
    @9
    vk
    cn
    @5
    cn
    wcel
    @8
    @5
    cr
    wcel
    #
    @11
    @9
    wi
    @5
    nnre
    @8
    @12
    wa
    @3
    @11
    @6
    @8
    @12
    @0
    @2
    @11
    @6
    wi
    #
    @0
    @8
    @12
    @2
    @13
    wi
    @0
    @8
    @12
    @2
    @11
    @6
    @0
    @8
    @12
    w3a
    @2
    @11
    wa
    cA
    @5
    clt
    wbr
    #
    @6
    cA
    @1
    @5
    lelttr
    @0
    @12
    @14
    @6
    wi
    @8
    cA
    @5
    ltle
    3adant2
    syld
    exp5o
    com3l
    imp4b
    com23
    sylan2
    reximdva
    mpd
    @3
    @6
    vk
    cn
    r19.35
    sylib
    rexlimiv
end
