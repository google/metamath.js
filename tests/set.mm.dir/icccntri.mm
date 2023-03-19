include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cdiv.mm"
include "wss.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "crp.mm"
include "wb.mm"
include "wa.mm"
include "icccntr.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem icccntri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume icccntri.1: |- A e. RR
  assume icccntri.2: |- B e. RR
  assume icccntri.3: |- R e. RR+
  assume icccntri.4: |- ( A / R ) = C
  assume icccntri.5: |- ( B / R ) = D


  assert |- ( X e. ( A [,] B ) -> ( X / R ) e. ( C [,] D ) )

  proof
    cX
    cr
    wcel
    #
    cX
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cX
    cR
    cdiv
    co
    cC
    cD
    cicc
    co
    wcel
    #
    @1
    cr
    cX
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @1
    cr
    wss
    icccntri.1
    icccntri.2
    cA
    cB
    iccssre
    mp2an
    sseli
    @0
    @2
    @3
    @0
    cR
    crp
    wcel
    #
    @2
    @3
    wb
    #
    icccntri.3
    @4
    @5
    @0
    @6
    wa
    @7
    icccntri.1
    icccntri.2
    cA
    cB
    cC
    cD
    cR
    cX
    icccntri.4
    icccntri.5
    icccntr
    mpanl12
    mpan2
    biimpd
    mpcom
end
