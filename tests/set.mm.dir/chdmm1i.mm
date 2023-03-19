include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "choccli.mm"
include "chub1i.mm"
include "chjcli.mm"
include "chsscon1i.mm"
include "mpbi.mm"
include "chub2i.mm"
include "ssini.mm"
include "chincli.mm"
include "inss1.mm"
include "chsscon3i.mm"
include "inss2.mm"
include "chlubii.mm"
include "mp2an.mm"
include "eqssi.mm"

theorem chdmm1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( A i^i B ) ) = ( ( _|_ ` A ) vH ( _|_ ` B ) )

  proof
    cA
    cB
    cin
    #
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    chj
    co
    #
    @4
    cort
    cfv
    #
    @0
    wss
    @1
    @4
    wss
    @5
    cA
    cB
    @2
    @4
    wss
    @5
    cA
    wss
    @2
    @3
    cA
    ch0le.1
    choccli
    #
    cB
    chjcl.2
    choccli
    #
    chub1i
    cA
    @4
    ch0le.1
    @2
    @3
    @6
    @7
    chjcli
    #
    chsscon1i
    mpbi
    @3
    @4
    wss
    @5
    cB
    wss
    @3
    @2
    @7
    @6
    chub2i
    cB
    @4
    chjcl.2
    @8
    chsscon1i
    mpbi
    ssini
    @4
    @0
    @8
    cA
    cB
    ch0le.1
    chjcl.2
    chincli
    #
    chsscon1i
    mpbi
    @2
    @1
    wss
    #
    @3
    @1
    wss
    #
    @4
    @1
    wss
    @0
    cA
    wss
    @10
    cA
    cB
    inss1
    @0
    cA
    @9
    ch0le.1
    chsscon3i
    mpbi
    @0
    cB
    wss
    @11
    cA
    cB
    inss2
    @0
    cB
    @9
    chjcl.2
    chsscon3i
    mpbi
    @2
    @3
    @1
    @6
    @7
    @0
    @9
    choccli
    chlubii
    mp2an
    eqssi
end
