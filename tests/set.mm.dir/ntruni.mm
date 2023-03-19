include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cnt.mm"
include "cfv.mm"
include "cuni.mm"
include "wral.mm"
include "ciun.mm"
include "elssuni.mm"
include "wi.mm"
include "sspwuni.mm"
include "ntrss.mm"
include "3expia.mm"
include "sylan2b.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"

theorem ntruni
  let vo: setvar o
  let cJ: class J
  let cO: class O
  let cX: class X
  assume ntruni.1: |- X = U. J

  disjoint J o
  disjoint O o
  disjoint X o
  assert |- ( ( J e. Top /\ O C_ ~P X ) -> U_ o e. O ( ( int ` J ) ` o ) C_ ( ( int ` J ) ` U. O ) )

  proof
    cJ
    ctop
    wcel
    #
    cO
    cX
    cpw
    wss
    #
    wa
    #
    vo
    cv
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    cO
    cuni
    #
    @4
    cfv
    #
    wss
    #
    vo
    cO
    wral
    vo
    cO
    @5
    ciun
    @7
    wss
    @2
    @8
    vo
    cO
    @3
    cO
    wcel
    @3
    @6
    wss
    #
    @2
    @8
    @3
    cO
    elssuni
    @1
    @0
    @6
    cX
    wss
    #
    @9
    @8
    wi
    cO
    cX
    sspwuni
    @0
    @10
    @9
    @8
    @6
    @3
    cJ
    cX
    ntruni.1
    ntrss
    3expia
    sylan2b
    syl5
    ralrimiv
    vo
    cO
    @5
    @7
    iunss
    sylibr
end
