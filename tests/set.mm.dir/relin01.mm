include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wo.mm"
include "w3o.mm"
include "1re.mm"
include "letric.mm"
include "mpan2.mm"
include "0re.mm"
include "pm3.21.mm"
include "orim2d.mm"
include "syl5com.mm"
include "orim1d.mm"
include "mpd.mm"
include "df-3or.mm"
include "sylibr.mm"

theorem relin01
  let cA: class A


  assert |- ( A e. RR -> ( A <_ 0 \/ ( 0 <_ A /\ A <_ 1 ) \/ 1 <_ A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    cle
    wbr
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    wa
    #
    wo
    #
    c1
    cA
    cle
    wbr
    #
    wo
    #
    @1
    @4
    @6
    w3o
    @0
    @3
    @6
    wo
    #
    @7
    @0
    c1
    cr
    wcel
    @8
    1re
    cA
    c1
    letric
    mpan2
    @0
    @3
    @5
    @6
    @0
    @1
    @2
    wo
    #
    @3
    @5
    @0
    cc0
    cr
    wcel
    @9
    0re
    cA
    cc0
    letric
    mpan2
    @3
    @2
    @4
    @1
    @3
    @2
    pm3.21
    orim2d
    syl5com
    orim1d
    mpd
    @1
    @4
    @6
    df-3or
    sylibr
end
