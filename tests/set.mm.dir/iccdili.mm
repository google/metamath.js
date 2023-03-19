include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cmul.mm"
include "wss.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "crp.mm"
include "wb.mm"
include "wa.mm"
include "iccdil.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem iccdili
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume iccdili.1: |- A e. RR
  assume iccdili.2: |- B e. RR
  assume iccdili.3: |- R e. RR+
  assume iccdili.4: |- ( A x. R ) = C
  assume iccdili.5: |- ( B x. R ) = D


  assert |- ( X e. ( A [,] B ) -> ( X x. R ) e. ( C [,] D ) )

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
    cmul
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
    iccdili.1
    iccdili.2
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
    iccdili.3
    @4
    @5
    @0
    @6
    wa
    @7
    iccdili.1
    iccdili.2
    cA
    cB
    cC
    cD
    cR
    cX
    iccdili.4
    iccdili.5
    iccdil
    mpanl12
    mpan2
    biimpd
    mpcom
end
