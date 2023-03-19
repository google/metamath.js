include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cpr.mm"
include "cind.mm"
include "cfv.mm"
include "indval.mm"
include "cr.mm"
include "1re.mm"
include "0re.mm"
include "ifpr.mm"
include "mp2an.mm"
include "prcom.mm"
include "eleqtri.mm"
include "a1i.mm"
include "fmpt3d.mm"

theorem indf
  let cA: class A
  let cO: class O
  let cV: class V
  let vx: setvar x


  assert |- ( ( O e. V /\ A C_ O ) -> ( ( _Ind ` O ) ` A ) : O --> { 0 , 1 } )

  proof
    cO
    cV
    wcel
    cA
    cO
    wss
    wa
    #
    vx
    cO
    vx
    cv
    #
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    cc0
    c1
    cpr
    #
    cA
    cO
    cind
    cfv
    cfv
    vx
    cA
    cO
    cV
    indval
    @3
    @4
    wcel
    @0
    @1
    cO
    wcel
    wa
    @3
    c1
    cc0
    cpr
    #
    @4
    c1
    cr
    wcel
    cc0
    cr
    wcel
    @3
    @5
    wcel
    1re
    0re
    @2
    c1
    cc0
    cr
    cr
    ifpr
    mp2an
    c1
    cc0
    prcom
    eleqtri
    a1i
    fmpt3d
end
