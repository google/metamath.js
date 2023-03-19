include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "caddc.mm"
include "wss.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "wb.mm"
include "wa.mm"
include "iccshftr.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem iccshftri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume iccshftri.1: |- A e. RR
  assume iccshftri.2: |- B e. RR
  assume iccshftri.3: |- R e. RR
  assume iccshftri.4: |- ( A + R ) = C
  assume iccshftri.5: |- ( B + R ) = D


  assert |- ( X e. ( A [,] B ) -> ( X + R ) e. ( C [,] D ) )

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
    caddc
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
    iccshftri.1
    iccshftri.2
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
    cr
    wcel
    #
    @2
    @3
    wb
    #
    iccshftri.3
    @4
    @5
    @0
    @6
    wa
    @7
    iccshftri.1
    iccshftri.2
    cA
    cB
    cC
    cD
    cR
    cX
    iccshftri.4
    iccshftri.5
    iccshftr
    mpanl12
    mpan2
    biimpd
    mpcom
end
