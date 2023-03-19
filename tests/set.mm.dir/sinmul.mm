include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cmul.mm"
include "cossub.mm"
include "cosadd.mm"
include "oveq12d.mm"
include "wceq.mm"
include "coscl.mm"
include "mulcl.mm"
include "syl2an.mm"
include "sincl.mm"
include "pnncan.mm"
include "3anidm23.mm"
include "2times.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "syl2anc.mm"
include "2cn.mm"
include "mulcom.mm"
include "sylancr.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan4.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqtr2d.mm"

theorem sinmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( sin ` A ) x. ( sin ` B ) ) = ( ( ( cos ` ( A - B ) ) - ( cos ` ( A + B ) ) ) / 2 ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cmin
    co
    ccos
    cfv
    #
    cA
    cB
    caddc
    co
    ccos
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    cA
    csin
    cfv
    #
    cB
    csin
    cfv
    #
    cmul
    co
    #
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @8
    @2
    @5
    @9
    c2
    cdiv
    @2
    @5
    cA
    ccos
    cfv
    #
    cB
    ccos
    cfv
    #
    cmul
    co
    #
    @8
    caddc
    co
    #
    @13
    @8
    cmin
    co
    #
    cmin
    co
    #
    c2
    @8
    cmul
    co
    #
    @9
    @2
    @3
    @14
    @4
    @15
    cmin
    cA
    cB
    cossub
    cA
    cB
    cosadd
    oveq12d
    @2
    @13
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @16
    @17
    wceq
    @0
    @11
    cc
    wcel
    @12
    cc
    wcel
    @18
    @1
    cA
    coscl
    cB
    coscl
    @11
    @12
    mulcl
    syl2an
    @0
    @6
    cc
    wcel
    @7
    cc
    wcel
    @19
    @1
    cA
    sincl
    cB
    sincl
    @6
    @7
    mulcl
    syl2an
    #
    @18
    @19
    wa
    @16
    @8
    @8
    caddc
    co
    #
    @17
    @18
    @19
    @16
    @21
    wceq
    @13
    @8
    @8
    pnncan
    3anidm23
    @19
    @17
    @21
    wceq
    @18
    @8
    2times
    adantl
    eqtr4d
    syl2anc
    @2
    c2
    cc
    wcel
    #
    @19
    @17
    @9
    wceq
    2cn
    @20
    c2
    @8
    mulcom
    sylancr
    3eqtrd
    oveq1d
    @2
    @19
    @10
    @8
    wceq
    #
    @20
    @19
    @22
    c2
    cc0
    wne
    @23
    2cn
    2ne0
    @8
    c2
    divcan4
    mp3an23
    syl
    eqtr2d
end
