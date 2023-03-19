include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imdistani.mm"
include "elrp.mm"
include "sylibr.mm"
include "jctil.mm"
include "simpr.mm"
include "0le1.mm"
include "modid.mm"
include "syl2anc.mm"

theorem 1mod
  let cN: class N


  assert |- ( ( N e. RR /\ 1 < N ) -> ( 1 mod N ) = 1 )

  proof
    cN
    cr
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    wa
    #
    c1
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    wa
    cc0
    c1
    cle
    wbr
    #
    @1
    wa
    c1
    cN
    cmo
    co
    c1
    wceq
    @2
    @4
    @3
    @2
    @0
    cc0
    cN
    clt
    wbr
    #
    wa
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
    @3
    @0
    @7
    @1
    wa
    @6
    wi
    0re
    1re
    cc0
    c1
    cN
    lttr
    mp3an12
    mpani
    imdistani
    cN
    elrp
    sylibr
    1re
    jctil
    @2
    @1
    @5
    @0
    @1
    simpr
    0le1
    jctil
    c1
    cN
    modid
    syl2anc
end
