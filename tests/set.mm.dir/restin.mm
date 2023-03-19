include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "cuni.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "restco.mm"
include "3com23.mm"
include "mpd3an3.mm"
include "restid.mm"
include "oveq1d.mm"
include "incom.mm"
include "oveq2i.mm"
include "a1i.mm"
include "3eqtr3d.mm"

theorem restin
  let cA: class A
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  assume restin.1: |- X = U. J


  assert |- ( ( J e. V /\ A e. W ) -> ( J |`t A ) = ( J |`t ( A i^i X ) ) )

  proof
    cJ
    cV
    wcel
    #
    cA
    cW
    wcel
    #
    wa
    #
    cJ
    cX
    crest
    co
    #
    cA
    crest
    co
    #
    cJ
    cX
    cA
    cin
    #
    crest
    co
    #
    cJ
    cA
    crest
    co
    cJ
    cA
    cX
    cin
    #
    crest
    co
    #
    @0
    @1
    cX
    cvv
    wcel
    #
    @4
    @6
    wceq
    #
    @0
    @9
    @1
    @0
    cX
    cJ
    cuni
    cvv
    restin.1
    cJ
    cV
    uniexg
    syl5eqel
    adantr
    @0
    @9
    @1
    @10
    cX
    cA
    cJ
    cV
    cvv
    cW
    restco
    3com23
    mpd3an3
    @2
    @3
    cJ
    cA
    crest
    @0
    @3
    cJ
    wceq
    @1
    cJ
    cV
    cX
    restin.1
    restid
    adantr
    oveq1d
    @6
    @8
    wceq
    @2
    @5
    @7
    cJ
    crest
    cX
    cA
    incom
    oveq2i
    a1i
    3eqtr3d
end
