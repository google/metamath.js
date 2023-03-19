include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "subid1.mm"
include "fveq2d.mm"
include "oveqan12d.mm"
include "wbr.mm"
include "caddc.mm"
include "0cn.mm"
include "abs3dif.mm"
include "mp3an2.mm"
include "cr.mm"
include "w3a.mm"
include "wb.mm"
include "subcl.mm"
include "mpan2.mm"
include "abscl.mm"
include "syl.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "lesubadd.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"

theorem abs2dif
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( abs ` A ) - ( abs ` B ) ) <_ ( abs ` ( A - B ) ) )

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
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cmin
    co
    #
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    cmin
    co
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    @0
    @1
    @4
    @8
    @6
    @9
    cmin
    @0
    @3
    cA
    cabs
    cA
    subid1
    fveq2d
    @1
    @5
    cB
    cabs
    cB
    subid1
    fveq2d
    oveqan12d
    @2
    @7
    @11
    cle
    wbr
    #
    @4
    @11
    @6
    caddc
    co
    cle
    wbr
    #
    @0
    cc0
    cc
    wcel
    #
    @1
    @13
    0cn
    cA
    cc0
    cB
    abs3dif
    mp3an2
    @2
    @4
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    w3a
    #
    @12
    @13
    wb
    @2
    @15
    @16
    wa
    @17
    @18
    @0
    @15
    @1
    @16
    @0
    @3
    cc
    wcel
    #
    @15
    @0
    @14
    @19
    0cn
    cA
    cc0
    subcl
    mpan2
    @3
    abscl
    syl
    @1
    @5
    cc
    wcel
    #
    @16
    @1
    @14
    @20
    0cn
    cB
    cc0
    subcl
    mpan2
    @5
    abscl
    syl
    anim12i
    @2
    @10
    cc
    wcel
    @17
    cA
    cB
    subcl
    @10
    abscl
    syl
    @15
    @16
    @17
    df-3an
    sylanbrc
    @4
    @6
    @11
    lesubadd
    syl
    mpbird
    eqbrtrrd
end
