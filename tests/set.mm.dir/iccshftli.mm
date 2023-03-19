include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cmin.mm"
include "wss.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "wb.mm"
include "wa.mm"
include "iccshftl.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem iccshftli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume iccshftli.1: |- A e. RR
  assume iccshftli.2: |- B e. RR
  assume iccshftli.3: |- R e. RR
  assume iccshftli.4: |- ( A - R ) = C
  assume iccshftli.5: |- ( B - R ) = D


  assert |- ( X e. ( A [,] B ) -> ( X - R ) e. ( C [,] D ) )

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
    cmin
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
    iccshftli.1
    iccshftli.2
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
    iccshftli.3
    @4
    @5
    @0
    @6
    wa
    @7
    iccshftli.1
    iccshftli.2
    cA
    cB
    cC
    cD
    cR
    cX
    iccshftli.4
    iccshftli.5
    iccshftl
    mpanl12
    mpan2
    biimpd
    mpcom
end
