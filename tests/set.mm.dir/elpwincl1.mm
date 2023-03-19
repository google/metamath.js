include "cin.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "elpwi.mm"
include "ssinss1.mm"
include "3syl.mm"
include "cvv.mm"
include "wb.mm"
include "inex1g.mm"
include "elpwg.mm"
include "mpbird.mm"

theorem elpwincl1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume elpwincl.1: |- ( ph -> A e. ~P C )


  assert |- ( ph -> ( A i^i B ) e. ~P C )

  proof
    wph
    cA
    cB
    cin
    #
    cC
    cpw
    #
    wcel
    #
    @0
    cC
    wss
    #
    wph
    cA
    @1
    wcel
    #
    cA
    cC
    wss
    @3
    elpwincl.1
    cA
    cC
    elpwi
    cA
    cB
    cC
    ssinss1
    3syl
    wph
    @4
    @0
    cvv
    wcel
    @2
    @3
    wb
    elpwincl.1
    cA
    cB
    @1
    inex1g
    @0
    cC
    cvv
    elpwg
    3syl
    mpbird
end
