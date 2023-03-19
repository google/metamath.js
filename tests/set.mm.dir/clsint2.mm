include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "cint.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "ciin.mm"
include "cuni.mm"
include "wi.mm"
include "sspwuni.mm"
include "elssuni.mm"
include "sstr2.mm"
include "syl.mm"
include "adantl.mm"
include "intss1.mm"
include "clsss.mm"
include "syl3an3.mm"
include "3com23.mm"
include "3expia.mm"
include "syld.mm"
include "impancom.mm"
include "sylan2b.mm"
include "ralrimiv.mm"
include "ssiin.mm"
include "sylibr.mm"

theorem clsint2
  let cC: class C
  let cJ: class J
  let cX: class X
  let vc: setvar c
  assume clsint2.1: |- X = U. J

  disjoint C c
  disjoint J c
  disjoint X c
  assert |- ( ( J e. Top /\ C C_ ~P X ) -> ( ( cls ` J ) ` |^| C ) C_ |^|_ c e. C ( ( cls ` J ) ` c ) )

  proof
    cJ
    ctop
    wcel
    #
    cC
    cX
    cpw
    wss
    #
    wa
    #
    cC
    cint
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    vc
    cv
    #
    @4
    cfv
    #
    wss
    #
    vc
    cC
    wral
    @5
    vc
    cC
    @7
    ciin
    wss
    @2
    @8
    vc
    cC
    @1
    @0
    cC
    cuni
    #
    cX
    wss
    #
    @6
    cC
    wcel
    #
    @8
    wi
    cC
    cX
    sspwuni
    @0
    @11
    @10
    @8
    @0
    @11
    wa
    @10
    @6
    cX
    wss
    #
    @8
    @11
    @10
    @12
    wi
    #
    @0
    @11
    @6
    @9
    wss
    @13
    @6
    cC
    elssuni
    @6
    @9
    cX
    sstr2
    syl
    adantl
    @0
    @11
    @12
    @8
    @0
    @12
    @11
    @8
    @11
    @0
    @12
    @3
    @6
    wss
    @8
    @6
    cC
    intss1
    @6
    @3
    cJ
    cX
    clsint2.1
    clsss
    syl3an3
    3com23
    3expia
    syld
    impancom
    sylan2b
    ralrimiv
    vc
    cC
    @7
    @5
    ssiin
    sylibr
end
