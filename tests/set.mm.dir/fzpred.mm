include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "cz.mm"
include "eluzel2.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "fzsplit2.mm"
include "mpancom.mm"
include "fzsn.mm"
include "syl.mm"
include "uneq1d.mm"
include "eqtrd.mm"

theorem fzpred
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( M ... N ) = ( { M } u. ( ( M + 1 ) ... N ) ) )

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
    cM
    cfz
    co
    #
    cM
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
    cM
    csn
    #
    @5
    cun
    @4
    @0
    wcel
    #
    @1
    @2
    @6
    wceq
    @1
    cM
    cz
    wcel
    #
    cM
    @0
    wcel
    @8
    cM
    cN
    eluzel2
    #
    cM
    uzid
    cM
    cM
    peano2uz
    3syl
    cM
    cM
    cN
    fzsplit2
    mpancom
    @1
    @3
    @7
    @5
    @1
    @9
    @3
    @7
    wceq
    @10
    cM
    fzsn
    syl
    uneq1d
    eqtrd
end
