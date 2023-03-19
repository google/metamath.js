include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmin.mm"
include "ccos.mm"
include "cfv.mm"
include "csin.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcli.mm"
include "mulcl.mm"
include "mpan2.mm"
include "coshalfpim.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "adddir.mm"
include "mp3an3.mm"
include "3adant3.mm"
include "oveq1.mm"
include "mulid2i.mm"
include "syl6eq.mm"
include "3ad2ant3.mm"
include "eqtr3d.mm"
include "wb.mm"
include "subadd.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "mpbird.mm"
include "fveq2d.mm"

theorem sincosq1eq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ ( A + B ) = 1 ) -> ( sin ` ( A x. ( _pi / 2 ) ) ) = ( cos ` ( B x. ( _pi / 2 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cB
    caddc
    co
    #
    c1
    wceq
    #
    w3a
    #
    cpi
    c2
    cdiv
    co
    #
    cA
    @5
    cmul
    co
    #
    cmin
    co
    #
    ccos
    cfv
    #
    @6
    csin
    cfv
    #
    cB
    @5
    cmul
    co
    #
    ccos
    cfv
    @0
    @1
    @8
    @9
    wceq
    #
    @3
    @0
    @6
    cc
    wcel
    #
    @11
    @0
    @5
    cc
    wcel
    #
    @12
    cpi
    c2
    picn
    2cn
    2ne0
    divcli
    #
    cA
    @5
    mulcl
    mpan2
    #
    @6
    coshalfpim
    syl
    3ad2ant1
    @4
    @7
    @10
    ccos
    @4
    @7
    @10
    wceq
    #
    @6
    @10
    caddc
    co
    #
    @5
    wceq
    #
    @4
    @2
    @5
    cmul
    co
    #
    @17
    @5
    @0
    @1
    @19
    @17
    wceq
    #
    @3
    @0
    @1
    @13
    @20
    @14
    cA
    cB
    @5
    adddir
    mp3an3
    3adant3
    @3
    @0
    @19
    @5
    wceq
    @1
    @3
    @19
    c1
    @5
    cmul
    co
    @5
    @2
    c1
    @5
    cmul
    oveq1
    @5
    @14
    mulid2i
    syl6eq
    3ad2ant3
    eqtr3d
    @0
    @1
    @16
    @18
    wb
    #
    @3
    @0
    @12
    @10
    cc
    wcel
    #
    @21
    @1
    @15
    @1
    @13
    @22
    @14
    cB
    @5
    mulcl
    mpan2
    @13
    @12
    @22
    @21
    @14
    @5
    @6
    @10
    subadd
    mp3an1
    syl2an
    3adant3
    mpbird
    fveq2d
    eqtr3d
end
