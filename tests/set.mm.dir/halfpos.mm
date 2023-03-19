include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "halfpos2.mm"
include "rehalfcl.mm"
include "ltaddposd.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "2halves.mm"
include "syl.mm"
include "breq2d.mm"
include "3bitrd.mm"

theorem halfpos
  let cA: class A


  assert |- ( A e. RR -> ( 0 < A <-> ( A / 2 ) < A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    cc0
    cA
    c2
    cdiv
    co
    #
    clt
    wbr
    @1
    @1
    @1
    caddc
    co
    #
    clt
    wbr
    @1
    cA
    clt
    wbr
    cA
    halfpos2
    @0
    @1
    @1
    cA
    rehalfcl
    #
    @3
    ltaddposd
    @0
    @2
    cA
    @1
    clt
    @0
    cA
    cc
    wcel
    @2
    cA
    wceq
    cA
    recn
    cA
    2halves
    syl
    breq2d
    3bitrd
end
