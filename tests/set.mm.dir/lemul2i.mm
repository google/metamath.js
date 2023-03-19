include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "lemul2.mm"
include "mp3an12.mm"
include "mpan.mm"

theorem lemul2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR


  assert |- ( 0 < C -> ( A <_ B <-> ( C x. A ) <_ ( C x. B ) ) )

  proof
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
    co
    cle
    wbr
    wb
    #
    ltmul1.3
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    wa
    @2
    ltplus1.1
    prodgt0.2
    cA
    cB
    cC
    lemul2
    mp3an12
    mpan
end
