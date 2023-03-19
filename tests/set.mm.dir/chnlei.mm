include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "wss.mm"
include "wa.mm"
include "wpss.mm"
include "chub1i.mm"
include "biantrur.mm"
include "chlejb1i.mm"
include "eqcom.mm"
include "chjcomi.mm"
include "eqeq2i.mm"
include "3bitri.mm"
include "notbii.mm"
include "dfpss2.mm"
include "3bitr4i.mm"

theorem chnlei
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( -. B C_ A <-> A C. ( A vH B ) )

  proof
    cA
    cA
    cB
    chj
    co
    #
    wceq
    #
    wn
    #
    cA
    @0
    wss
    #
    @2
    wa
    cB
    cA
    wss
    #
    wn
    cA
    @0
    wpss
    @3
    @2
    cA
    cB
    ch0le.1
    chjcl.2
    chub1i
    biantrur
    @4
    @1
    @4
    cB
    cA
    chj
    co
    #
    cA
    wceq
    cA
    @5
    wceq
    @1
    cB
    cA
    chjcl.2
    ch0le.1
    chlejb1i
    @5
    cA
    eqcom
    @5
    @0
    cA
    cB
    cA
    chjcl.2
    ch0le.1
    chjcomi
    eqeq2i
    3bitri
    notbii
    cA
    @0
    dfpss2
    3bitr4i
end
