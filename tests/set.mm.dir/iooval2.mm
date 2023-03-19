include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "iooval.mm"
include "cin.mm"
include "inrab2.mm"
include "wceq.mm"
include "wss.mm"
include "ressxr.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "elioore.mm"
include "ssriv.mm"
include "syl6eqssr.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5reqr.mm"
include "eqtrd.mm"

theorem iooval2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A (,) B ) = { x e. RR | ( A < x /\ x < B ) } )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cA
    cB
    cioo
    co
    #
    cA
    vx
    cv
    #
    clt
    wbr
    @2
    cB
    clt
    wbr
    wa
    #
    vx
    cxr
    crab
    #
    @3
    vx
    cr
    crab
    #
    vx
    cA
    cB
    iooval
    #
    @0
    @5
    @4
    cr
    cin
    #
    @4
    @7
    @3
    vx
    cxr
    cr
    cin
    #
    crab
    #
    @5
    @3
    vx
    cxr
    cr
    inrab2
    @8
    cr
    wceq
    #
    @9
    @5
    wceq
    cr
    cxr
    wss
    @10
    ressxr
    cr
    cxr
    sseqin2
    mpbi
    @3
    vx
    @8
    cr
    rabeq
    ax-mp
    eqtri
    @0
    @4
    cr
    wss
    @7
    @4
    wceq
    @0
    @4
    @1
    cr
    @6
    vx
    @1
    cr
    @2
    cA
    cB
    elioore
    ssriv
    syl6eqssr
    @4
    cr
    df-ss
    sylib
    syl5reqr
    eqtrd
end
