include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cin.mm"
include "cnt.mm"
include "cfv.mm"
include "inss1.mm"
include "ntrss.mm"
include "mp3an3.mm"
include "3adant3.mm"
include "inss2.mm"
include "3adant2.mm"
include "ssind.mm"
include "simp1.mm"
include "ssinss1.mm"
include "3ad2ant2.mm"
include "ntropn.mm"
include "inopn.mm"
include "syl3anc.mm"
include "ntrss2.mm"
include "syl5ss.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "eqssd.mm"

theorem ntrin
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X /\ B C_ X ) -> ( ( int ` J ) ` ( A i^i B ) ) = ( ( ( int ` J ) ` A ) i^i ( ( int ` J ) ` B ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    cB
    cX
    wss
    #
    w3a
    #
    cA
    cB
    cin
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    cA
    @5
    cfv
    #
    cB
    @5
    cfv
    #
    cin
    #
    @3
    @6
    @7
    @8
    @0
    @1
    @6
    @7
    wss
    #
    @2
    @0
    @1
    @4
    cA
    wss
    @10
    cA
    cB
    inss1
    cA
    @4
    cJ
    cX
    clscld.1
    ntrss
    mp3an3
    3adant3
    @0
    @2
    @6
    @8
    wss
    #
    @1
    @0
    @2
    @4
    cB
    wss
    @11
    cA
    cB
    inss2
    cB
    @4
    cJ
    cX
    clscld.1
    ntrss
    mp3an3
    3adant2
    ssind
    @3
    @0
    @4
    cX
    wss
    #
    @9
    cJ
    wcel
    #
    @9
    @4
    wss
    @9
    @6
    wss
    @0
    @1
    @2
    simp1
    #
    @1
    @0
    @12
    @2
    cA
    cB
    cX
    ssinss1
    3ad2ant2
    @3
    @0
    @7
    cJ
    wcel
    #
    @8
    cJ
    wcel
    #
    @13
    @14
    @0
    @1
    @15
    @2
    cA
    cJ
    cX
    clscld.1
    ntropn
    3adant3
    @0
    @2
    @16
    @1
    cB
    cJ
    cX
    clscld.1
    ntropn
    3adant2
    @7
    @8
    cJ
    inopn
    syl3anc
    @3
    @9
    cA
    cB
    @3
    @9
    @7
    cA
    @7
    @8
    inss1
    @0
    @1
    @7
    cA
    wss
    @2
    cA
    cJ
    cX
    clscld.1
    ntrss2
    3adant3
    syl5ss
    @3
    @9
    @8
    cB
    @7
    @8
    inss2
    @0
    @2
    @8
    cB
    wss
    @1
    cB
    cJ
    cX
    clscld.1
    ntrss2
    3adant2
    syl5ss
    ssind
    @4
    cJ
    @9
    cX
    clscld.1
    ssntr
    syl22anc
    eqssd
end
