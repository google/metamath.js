include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cun.mm"
include "c3.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "1le2.mm"
include "a1i.mm"
include "eluzle.mm"
include "cz.mm"
include "wa.mm"
include "wb.mm"
include "eluzelz.mm"
include "2z.mm"
include "1z.mm"
include "elfz.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpbir2and.mm"
include "fzsplit.mm"
include "df-3.mm"
include "oveq1i.mm"
include "uneq2i.mm"
include "syl6eqr.mm"

theorem axlowdimlem3
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( 1 ... N ) = ( ( 1 ... 2 ) u. ( 3 ... N ) ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    c1
    cN
    cfz
    co
    #
    c1
    c2
    cfz
    co
    #
    c2
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cun
    #
    @2
    c3
    cN
    cfz
    co
    #
    cun
    @0
    c2
    @1
    wcel
    #
    @1
    @5
    wceq
    @0
    @7
    c1
    c2
    cle
    wbr
    #
    c2
    cN
    cle
    wbr
    #
    @8
    @0
    1le2
    a1i
    c2
    cN
    eluzle
    @0
    cN
    cz
    wcel
    #
    @7
    @8
    @9
    wa
    wb
    #
    c2
    cN
    eluzelz
    c2
    cz
    wcel
    c1
    cz
    wcel
    @10
    @11
    2z
    1z
    c2
    c1
    cN
    elfz
    mp3an12
    syl
    mpbir2and
    c2
    c1
    cN
    fzsplit
    syl
    @6
    @4
    @2
    c3
    @3
    cN
    cfz
    df-3
    oveq1i
    uneq2i
    syl6eqr
end
