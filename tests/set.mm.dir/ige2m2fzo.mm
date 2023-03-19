include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "eluzel2.mm"
include "1z.mm"
include "jctir.mm"
include "1lt2.mm"
include "jctr.mm"
include "eluzgtdifelfzo.mm"
include "sylc.mm"

theorem ige2m2fzo
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( N - 2 ) e. ( 0 ..^ ( N - 1 ) ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    c2
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    wa
    @0
    c1
    c2
    clt
    wbr
    #
    wa
    cN
    c2
    cmin
    co
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    wcel
    @0
    @1
    @2
    c2
    cN
    eluzel2
    1z
    jctir
    @0
    @3
    1lt2
    jctr
    c2
    c1
    cN
    eluzgtdifelfzo
    sylc
end
