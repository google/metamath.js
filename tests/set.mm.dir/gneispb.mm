include "ctop.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "cpw.mm"
include "wa.mm"
include "3simpb.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "elpwid.mm"
include "ssnei2.mm"
include "syl12anc.mm"
include "exp31.mm"
include "ralrimiv.mm"

theorem gneispb
  let cP: class P
  let cJ: class J
  let cN: class N
  let cX: class X
  let vs: setvar s
  assume gneispace.x: |- X = U. J

  disjoint J s
  disjoint N s
  disjoint P s
  disjoint X s
  assert |- ( ( J e. Top /\ P e. X /\ N e. ( ( nei ` J ) ` { P } ) ) -> A. s e. ~P X ( N C_ s -> s e. ( ( nei ` J ) ` { P } ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cP
    cX
    wcel
    #
    cN
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    w3a
    #
    cN
    vs
    cv
    #
    wss
    #
    @6
    @3
    wcel
    #
    wi
    vs
    cX
    cpw
    #
    @5
    @6
    @9
    wcel
    #
    @7
    @8
    @5
    @10
    wa
    #
    @7
    wa
    #
    @0
    @4
    wa
    #
    @7
    @6
    cX
    wss
    @8
    @5
    @13
    @10
    @7
    @0
    @1
    @4
    3simpb
    ad2antrr
    @11
    @7
    simpr
    @12
    @6
    cX
    @5
    @10
    @7
    simplr
    elpwid
    @2
    cJ
    @6
    cN
    cX
    gneispace.x
    ssnei2
    syl12anc
    exp31
    ralrimiv
end
