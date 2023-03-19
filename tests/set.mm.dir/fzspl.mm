include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "eluzelz.mm"
include "zcnd.mm"
include "1zzd.mm"
include "npcand.mm"
include "eleq1d.mm"
include "ibir.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelre.mm"
include "lem1d.mm"
include "wa.mm"
include "wb.mm"
include "zsubcld.mm"
include "eluz1.mm"
include "syl.mm"
include "mpbir2and.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fzsn.mm"
include "eqtrd.mm"
include "uneq2d.mm"

theorem fzspl
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( M ... N ) = ( ( M ... ( N - 1 ) ) u. { N } ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cN
    cfz
    co
    #
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @3
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
    @4
    cN
    csn
    #
    cun
    @1
    @5
    @0
    wcel
    #
    cN
    @3
    cuz
    cfv
    wcel
    #
    @2
    @7
    wceq
    @1
    @9
    @1
    @5
    cN
    @0
    @1
    cN
    c1
    @1
    cN
    cM
    cN
    eluzelz
    #
    zcnd
    @1
    c1
    @1
    1zzd
    #
    zcnd
    npcand
    #
    eleq1d
    ibir
    @1
    @10
    cN
    cz
    wcel
    #
    @3
    cN
    cle
    wbr
    #
    @11
    @1
    cN
    cM
    cN
    eluzelre
    lem1d
    @1
    @3
    cz
    wcel
    @10
    @14
    @15
    wa
    wb
    @1
    cN
    c1
    @11
    @12
    zsubcld
    @3
    cN
    eluz1
    syl
    mpbir2and
    @3
    cM
    cN
    fzsplit2
    syl2anc
    @1
    @6
    @8
    @4
    @1
    @6
    cN
    cN
    cfz
    co
    #
    @8
    @1
    @5
    cN
    cN
    cfz
    @13
    oveq1d
    @1
    @14
    @16
    @8
    wceq
    @11
    cN
    fzsn
    syl
    eqtrd
    uneq2d
    eqtrd
end
