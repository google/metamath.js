include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "wss.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwi.mm"
include "simpl.mm"
include "simpr.mm"
include "unssd.mm"
include "syl2an.mm"
include "wb.mm"
include "inss2.mm"
include "unfi.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "elind.mm"

theorem ackbij1lem6
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H


  assert |- ( ( A e. ( ~P _om i^i Fin ) /\ B e. ( ~P _om i^i Fin ) ) -> ( A u. B ) e. ( ~P _om i^i Fin ) )

  proof
    cA
    com
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    @0
    cfn
    cA
    cB
    cun
    #
    @4
    @5
    @0
    wcel
    #
    @5
    com
    wss
    #
    @2
    cA
    @0
    wcel
    #
    cB
    @0
    wcel
    #
    @7
    @3
    @1
    @0
    cA
    @0
    cfn
    inss1
    #
    sseli
    @1
    @0
    cB
    @10
    sseli
    @8
    cA
    com
    wss
    #
    cB
    com
    wss
    #
    @7
    @9
    cA
    com
    elpwi
    cB
    com
    elpwi
    @11
    @12
    wa
    cA
    cB
    com
    @11
    @12
    simpl
    @11
    @12
    simpr
    unssd
    syl2an
    syl2an
    @4
    @5
    cfn
    wcel
    #
    @6
    @7
    wb
    @2
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    @13
    @3
    @1
    cfn
    cA
    @0
    cfn
    inss2
    #
    sseli
    @1
    cfn
    cB
    @14
    sseli
    cA
    cB
    unfi
    syl2an
    #
    @5
    com
    cfn
    elpwg
    syl
    mpbird
    @15
    elind
end
