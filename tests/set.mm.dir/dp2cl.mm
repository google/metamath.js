include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "df-dp2.mm"
include "wne.mm"
include "10re.mm"
include "10pos.mm"
include "gt0ne0ii.mm"
include "redivcl.mm"
include "mp3an23.mm"
include "readdcl.mm"
include "sylan2.mm"
include "syl5eqel.mm"

theorem dp2cl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> _ A B e. RR )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    cB
    cdp2
    cA
    cB
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    cr
    cA
    cB
    df-dp2
    @1
    @0
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    @1
    @2
    cr
    wcel
    @2
    cc0
    wne
    @5
    10re
    @2
    10re
    10pos
    gt0ne0ii
    cB
    @2
    redivcl
    mp3an23
    cA
    @3
    readdcl
    sylan2
    syl5eqel
end
