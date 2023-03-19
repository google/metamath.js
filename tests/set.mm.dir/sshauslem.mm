include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wf1.mm"
include "ccn.mm"
include "co.mm"
include "simp1.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "mp1i.mm"
include "simp3.mm"
include "wb.mm"
include "simp2.mm"
include "ctop.mm"
include "3ad2ant1.mm"
include "toptopon.mm"
include "sylib.mm"
include "ssidcn.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "syl3anc.mm"

theorem sshauslem
  let cA: class A
  let cJ: class J
  let cK: class K
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  assume t1sep.1: |- X = U. J
  assume sshauslem.2: |- ( J e. A -> J e. Top )
  assume sshauslem.3: |- ( ( J e. A /\ ( _I |` X ) : X -1-1-> X /\ ( _I |` X ) e. ( K Cn J ) ) -> K e. A )


  assert |- ( ( J e. A /\ K e. ( TopOn ` X ) /\ J C_ K ) -> K e. A )

  proof
    cJ
    cA
    wcel
    #
    cK
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    cK
    wss
    #
    w3a
    #
    @0
    cX
    cX
    cid
    cX
    cres
    #
    wf1
    #
    @5
    cK
    cJ
    ccn
    co
    wcel
    #
    cK
    cA
    wcel
    @0
    @2
    @3
    simp1
    cX
    cX
    @5
    wf1o
    @6
    @4
    cX
    f1oi
    cX
    cX
    @5
    f1of1
    mp1i
    @4
    @7
    @3
    @0
    @2
    @3
    simp3
    @4
    @2
    cJ
    @1
    wcel
    #
    @7
    @3
    wb
    @0
    @2
    @3
    simp2
    @4
    cJ
    ctop
    wcel
    #
    @8
    @0
    @2
    @9
    @3
    sshauslem.2
    3ad2ant1
    cJ
    cX
    t1sep.1
    toptopon
    sylib
    cK
    cJ
    cX
    ssidcn
    syl2anc
    mpbird
    sshauslem.3
    syl3anc
end
