include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "eluzelre.mm"
include "resqcld.mm"
include "1red.mm"
include "resubcld.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "sq1.mm"
include "cz.mm"
include "eluz2b1.mm"
include "simprbi.mm"
include "cle.mm"
include "0le1.mm"
include "a1i.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "lt2sqd.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "posdifd.mm"
include "elrpd.mm"

theorem rmspecpos
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( ( A ^ 2 ) - 1 ) e. RR+ )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cA
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    @0
    @1
    c1
    @0
    cA
    c2
    cA
    eluzelre
    #
    resqcld
    #
    @0
    1red
    #
    resubcld
    @0
    c1
    @1
    clt
    wbr
    cc0
    @2
    clt
    wbr
    @0
    c1
    c1
    c2
    cexp
    co
    #
    @1
    clt
    sq1
    @0
    c1
    cA
    clt
    wbr
    #
    @6
    @1
    clt
    wbr
    @0
    cA
    cz
    wcel
    @7
    cA
    eluz2b1
    simprbi
    @0
    c1
    cA
    @5
    @3
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    @0
    cA
    cA
    eluzge2nn0
    nn0ge0d
    lt2sqd
    mpbid
    syl5eqbrr
    @0
    c1
    @1
    @5
    @4
    posdifd
    mpbid
    elrpd
end
