include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cfzo.mm"
include "wss.mm"
include "cz.mm"
include "caddc.mm"
include "eluzel2.mm"
include "peano2zm.mm"
include "syl.mm"
include "1zzd.mm"
include "id.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "eluzsub.mm"
include "syl3anc.mm"
include "fzss2.mm"
include "fzoval.mm"
include "eluzelz.mm"
include "3sstr4d.mm"

theorem fzoss2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` K ) -> ( M ..^ K ) C_ ( M ..^ N ) )

  proof
    cN
    cK
    cuz
    cfv
    #
    wcel
    #
    cM
    cK
    c1
    cmin
    co
    #
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
    cM
    cK
    cfzo
    co
    #
    cM
    cN
    cfzo
    co
    #
    @1
    @4
    @2
    cuz
    cfv
    wcel
    #
    @3
    @5
    wss
    @1
    @2
    cz
    wcel
    #
    c1
    cz
    wcel
    cN
    @2
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @8
    @1
    cK
    cz
    wcel
    #
    @9
    cK
    cN
    eluzel2
    #
    cK
    peano2zm
    syl
    @1
    1zzd
    @1
    cN
    @0
    @11
    @1
    id
    @1
    @10
    cK
    cuz
    @1
    cK
    cc
    wcel
    c1
    cc
    wcel
    @10
    cK
    wceq
    @1
    cK
    @13
    zcnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    fveq2d
    eleqtrrd
    c1
    @2
    cN
    eluzsub
    syl3anc
    @2
    cM
    @4
    fzss2
    syl
    @1
    @12
    @6
    @3
    wceq
    @13
    cM
    cK
    fzoval
    syl
    @1
    cN
    cz
    wcel
    @7
    @5
    wceq
    cK
    cN
    eluzelz
    cM
    cN
    fzoval
    syl
    3sstr4d
end
