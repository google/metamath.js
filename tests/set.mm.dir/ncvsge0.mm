include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "elinel1.mm"
include "adantr.mm"
include "ncvsprp.mm"
include "syl3an2.mm"
include "elinel2.mm"
include "absid.mm"
include "sylan.mm"
include "3ad2ant2.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem ncvsge0
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume ncvsprp.v: |- V = ( Base ` W )
  assume ncvsprp.n: |- N = ( norm ` W )
  assume ncvsprp.s: |- .x. = ( .s ` W )
  assume ncvsprp.f: |- F = ( Scalar ` W )
  assume ncvsprp.k: |- K = ( Base ` F )


  assert |- ( ( W e. ( NrmVec i^i CVec ) /\ ( A e. ( K i^i RR ) /\ 0 <_ A ) /\ B e. V ) -> ( N ` ( A .x. B ) ) = ( A x. ( N ` B ) ) )

  proof
    cW
    cnvc
    ccvs
    cin
    wcel
    #
    cA
    cK
    cr
    cin
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    c.x
    co
    cN
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cN
    cfv
    #
    cmul
    co
    #
    cA
    @8
    cmul
    co
    @3
    @0
    cA
    cK
    wcel
    #
    @4
    @6
    @9
    wceq
    @1
    @10
    @2
    cA
    cK
    cr
    elinel1
    adantr
    cA
    cB
    c.x
    cF
    cK
    cN
    cV
    cW
    ncvsprp.v
    ncvsprp.n
    ncvsprp.s
    ncvsprp.f
    ncvsprp.k
    ncvsprp
    syl3an2
    @5
    @7
    cA
    @8
    cmul
    @3
    @0
    @7
    cA
    wceq
    #
    @4
    @1
    cA
    cr
    wcel
    @2
    @11
    cA
    cK
    cr
    elinel2
    cA
    absid
    sylan
    3ad2ant2
    oveq1d
    eqtrd
end
