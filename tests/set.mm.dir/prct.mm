include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "com.mm"
include "cdom.mm"
include "df-pr.mm"
include "wbr.mm"
include "snct.mm"
include "unctb.mm"
include "syl2an.mm"
include "syl5eqbr.mm"

theorem prct
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> { A , B } ~<_ _om )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cA
    cB
    cpr
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    com
    cdom
    cA
    cB
    df-pr
    @0
    @2
    com
    cdom
    wbr
    @3
    com
    cdom
    wbr
    @4
    com
    cdom
    wbr
    @1
    cA
    cV
    snct
    cB
    cW
    snct
    @2
    @3
    unctb
    syl2an
    syl5eqbr
end
