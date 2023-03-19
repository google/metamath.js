include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "csn.mm"
include "cun.mm"
include "c2.mm"
include "ctp.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzsuc.mm"
include "3syl.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an23.mm"
include "syl.mm"
include "df-2.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "cpr.mm"
include "fzpr.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "df-tp.mm"
include "3eqtr3d.mm"

theorem fztp
  let cM: class M
  let vm: setvar m


  assert |- ( M e. ZZ -> ( M ... ( M + 2 ) ) = { M , ( M + 1 ) , ( M + 2 ) } )

  proof
    cM
    cz
    wcel
    #
    cM
    cM
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    cM
    @1
    cfz
    co
    #
    @2
    csn
    #
    cun
    #
    cM
    cM
    c2
    caddc
    co
    #
    cfz
    co
    cM
    @1
    @7
    ctp
    #
    @0
    cM
    cM
    cuz
    cfv
    #
    wcel
    @1
    @9
    wcel
    @3
    @6
    wceq
    cM
    uzid
    cM
    cM
    peano2uz
    cM
    @1
    fzsuc
    3syl
    @0
    @2
    @7
    cM
    cfz
    @0
    @2
    cM
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @7
    @0
    cM
    cc
    wcel
    #
    @2
    @11
    wceq
    #
    cM
    zcn
    @12
    c1
    cc
    wcel
    #
    @14
    @13
    ax-1cn
    ax-1cn
    cM
    c1
    c1
    addass
    mp3an23
    syl
    c2
    @10
    cM
    caddc
    df-2
    oveq2i
    syl6eqr
    #
    oveq2d
    @0
    @6
    cM
    @1
    cpr
    #
    @7
    csn
    #
    cun
    @8
    @0
    @4
    @16
    @5
    @17
    cM
    fzpr
    @0
    @2
    @7
    @15
    sneqd
    uneq12d
    cM
    @1
    @7
    df-tp
    syl6eqr
    3eqtr3d
end
