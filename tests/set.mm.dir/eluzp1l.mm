include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "eluzle.mm"
include "adantl.mm"
include "wb.mm"
include "eluzelz.mm"
include "zltp1le.mm"
include "sylan2.mm"
include "mpbird.mm"

theorem eluzp1l
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ( ZZ>= ` ( M + 1 ) ) ) -> M < N )

  proof
    cM
    cz
    wcel
    #
    cN
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wa
    cM
    cN
    clt
    wbr
    #
    @1
    cN
    cle
    wbr
    #
    @2
    @4
    @0
    @1
    cN
    eluzle
    adantl
    @2
    @0
    cN
    cz
    wcel
    @3
    @4
    wb
    @1
    cN
    eluzelz
    cM
    cN
    zltp1le
    sylan2
    mpbird
end
