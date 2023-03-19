include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cfl.mm"
include "c5.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "cdc.mm"
include "c3.mm"
include "c6.mm"
include "cn0.mm"
include "wb.mm"
include "5nn0.mm"
include "flsqrt.mm"
include "mpan2.mm"
include "cmul.mm"
include "5cn.mm"
include "sqvali.mm"
include "5t5e25.mm"
include "eqtri.mm"
include "breq1i.mm"
include "a1i.mm"
include "5p1e6.mm"
include "oveq1i.mm"
include "6cn.mm"
include "6t6e36.mm"
include "breq2i.mm"
include "anbi12d.mm"
include "bitr2d.mm"

theorem flsqrt5
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( X e. RR /\ 0 <_ X ) -> ( ( ; 2 5 <_ X /\ X < ; 3 6 ) <-> ( |_ ` ( sqrt ` X ) ) = 5 ) )

  proof
    cX
    cr
    wcel
    cc0
    cX
    cle
    wbr
    wa
    #
    cX
    csqrt
    cfv
    cfl
    cfv
    c5
    wceq
    #
    c5
    c2
    cexp
    co
    #
    cX
    cle
    wbr
    #
    cX
    c5
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    clt
    wbr
    #
    wa
    #
    c2
    c5
    cdc
    #
    cX
    cle
    wbr
    #
    cX
    c3
    c6
    cdc
    #
    clt
    wbr
    #
    wa
    @0
    c5
    cn0
    wcel
    @1
    @7
    wb
    5nn0
    cX
    c5
    flsqrt
    mpan2
    @0
    @3
    @9
    @6
    @11
    @3
    @9
    wb
    @0
    @2
    @8
    cX
    cle
    @2
    c5
    c5
    cmul
    co
    @8
    c5
    5cn
    sqvali
    5t5e25
    eqtri
    breq1i
    a1i
    @6
    @11
    wb
    @0
    @5
    @10
    cX
    clt
    @5
    c6
    c2
    cexp
    co
    #
    @10
    @4
    c6
    c2
    cexp
    5p1e6
    oveq1i
    @12
    c6
    c6
    cmul
    co
    @10
    c6
    6cn
    sqvali
    6t6e36
    eqtri
    eqtri
    breq2i
    a1i
    anbi12d
    bitr2d
end
