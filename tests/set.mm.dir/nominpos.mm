include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wrex.mm"
include "wn.mm"
include "wcel.mm"
include "wi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "rehalfcl.mm"
include "2re.mm"
include "2pos.mm"
include "divgt0.mm"
include "mpanr12.mm"
include "ex.mm"
include "halfpos.mm"
include "biimpd.mm"
include "jcad.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "iman.mm"
include "sylib.mm"
include "nrex.mm"

theorem nominpos
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- -. E. x e. RR ( 0 < x /\ -. E. y e. RR ( 0 < y /\ y < x ) )

  proof
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    cc0
    vy
    cv
    #
    clt
    wbr
    #
    @2
    @0
    clt
    wbr
    #
    wa
    #
    vy
    cr
    wrex
    #
    wn
    wa
    #
    vx
    cr
    @0
    cr
    wcel
    #
    @1
    @6
    wi
    @7
    wn
    @8
    @0
    c2
    cdiv
    co
    #
    cr
    wcel
    @1
    cc0
    @9
    clt
    wbr
    #
    @9
    @0
    clt
    wbr
    #
    wa
    #
    @6
    @0
    rehalfcl
    @8
    @1
    @10
    @11
    @8
    @1
    @10
    @8
    @1
    wa
    c2
    cr
    wcel
    cc0
    c2
    clt
    wbr
    @10
    2re
    2pos
    @0
    c2
    divgt0
    mpanr12
    ex
    @8
    @1
    @11
    @0
    halfpos
    biimpd
    jcad
    @5
    @12
    vy
    @9
    cr
    @2
    @9
    wceq
    @3
    @10
    @4
    @11
    @2
    @9
    cc0
    clt
    breq2
    @2
    @9
    @0
    clt
    breq1
    anbi12d
    rspcev
    syl6an
    @1
    @6
    iman
    sylib
    nrex
end
