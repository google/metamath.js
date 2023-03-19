include "cun.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "unss.mm"
include "wi.mm"
include "ssrelrel.mm"
include "bi2anan9.mm"
include "eqss.mm"
include "2albiim.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "sylbir.mm"

theorem eqrelrel
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  assert |- ( ( A u. B ) C_ ( ( _V X. _V ) X. _V ) -> ( A = B <-> A. x A. y A. z ( <. <. x , y >. , z >. e. A <-> <. <. x , y >. , z >. e. B ) ) )

  proof
    cA
    cB
    cun
    cvv
    cvv
    cxp
    cvv
    cxp
    #
    wss
    cA
    @0
    wss
    #
    cB
    @0
    wss
    #
    wa
    #
    cA
    cB
    wceq
    #
    vx
    cv
    vy
    cv
    cop
    vz
    cv
    cop
    #
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wb
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    wb
    cA
    cB
    @0
    unss
    @3
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    @6
    @7
    wi
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    @7
    @6
    wi
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    wa
    #
    @4
    @9
    @1
    @10
    @13
    @2
    @11
    @15
    vx
    vy
    vz
    cA
    cB
    ssrelrel
    vx
    vy
    vz
    cB
    cA
    ssrelrel
    bi2anan9
    cA
    cB
    eqss
    @9
    @12
    @14
    wa
    #
    vx
    wal
    @16
    @8
    @17
    vx
    @6
    @7
    vy
    vz
    2albiim
    albii
    @12
    @14
    vx
    19.26
    bitri
    3bitr4g
    sylbir
end
