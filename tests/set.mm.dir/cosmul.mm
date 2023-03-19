include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "ccos.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "caddc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wceq.mm"
include "coscl.mm"
include "mulcl.mm"
include "syl2an.mm"
include "2cnne0.mm"
include "a1i.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "divcan3.mm"
include "syl.mm"
include "csin.mm"
include "sincl.mm"
include "ppncand.mm"
include "cossub.mm"
include "cosadd.mm"
include "oveq12d.mm"
include "2timesd.mm"
include "3eqtr4rd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem cosmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( cos ` A ) x. ( cos ` B ) ) = ( ( ( cos ` ( A - B ) ) + ( cos ` ( A + B ) ) ) / 2 ) )

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
    c2
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
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @5
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
    caddc
    co
    #
    c2
    cdiv
    co
    @2
    @5
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    w3a
    #
    @7
    @5
    wceq
    @2
    @11
    @12
    @13
    wa
    #
    @14
    @0
    @3
    cc
    wcel
    @4
    cc
    wcel
    @11
    @1
    cA
    coscl
    cB
    coscl
    @3
    @4
    mulcl
    syl2an
    #
    @15
    @2
    2cnne0
    a1i
    @11
    @12
    @13
    3anass
    sylanbrc
    @5
    c2
    divcan3
    syl
    @2
    @6
    @10
    c2
    cdiv
    @2
    @5
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
    caddc
    co
    #
    @5
    @19
    cmin
    co
    #
    caddc
    co
    @5
    @5
    caddc
    co
    @10
    @6
    @2
    @5
    @19
    @5
    @16
    @0
    @17
    cc
    wcel
    @18
    cc
    wcel
    @19
    cc
    wcel
    @1
    cA
    sincl
    cB
    sincl
    @17
    @18
    mulcl
    syl2an
    @16
    ppncand
    @2
    @8
    @20
    @9
    @21
    caddc
    cA
    cB
    cossub
    cA
    cB
    cosadd
    oveq12d
    @2
    @5
    @16
    2timesd
    3eqtr4rd
    oveq1d
    eqtr3d
end
