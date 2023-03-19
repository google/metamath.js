include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "cdiv.mm"
include "co.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imdistani.mm"
include "recgt0.mm"
include "syl.mm"
include "recgt1.mm"
include "biimpa.mm"
include "sylancom.mm"
include "jca.mm"

theorem recgt1i
  let cA: class A


  assert |- ( ( A e. RR /\ 1 < A ) -> ( 0 < ( 1 / A ) /\ ( 1 / A ) < 1 ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    cc0
    c1
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    @3
    c1
    clt
    wbr
    #
    @2
    @0
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @4
    @0
    @1
    @6
    @0
    cc0
    c1
    clt
    wbr
    #
    @1
    @6
    0lt1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    @8
    @1
    wa
    @6
    wi
    0re
    1re
    cc0
    c1
    cA
    lttr
    mp3an12
    mpani
    imdistani
    #
    cA
    recgt0
    syl
    @0
    @1
    @7
    @5
    @9
    @7
    @1
    @5
    cA
    recgt1
    biimpa
    sylancom
    jca
end
