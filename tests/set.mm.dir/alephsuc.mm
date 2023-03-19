include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "char.mm"
include "com.mm"
include "crdg.mm"
include "cfv.mm"
include "cale.mm"
include "rdgsuc.mm"
include "df-aleph.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem alephsuc
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. On -> ( aleph ` suc A ) = ( har ` ( aleph ` A ) ) )

  proof
    cA
    con0
    wcel
    cA
    csuc
    #
    char
    com
    crdg
    #
    cfv
    cA
    @1
    cfv
    #
    char
    cfv
    @0
    cale
    cfv
    cA
    cale
    cfv
    #
    char
    cfv
    com
    cA
    char
    rdgsuc
    @0
    cale
    @1
    df-aleph
    fveq1i
    @3
    @2
    char
    cA
    cale
    @1
    df-aleph
    fveq1i
    fveq2i
    3eqtr4g
end
