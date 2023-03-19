include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "odd2np1.mm"
include "bi2anan9.mm"
include "reeanv.mm"
include "2z.mm"
include "zsubcl.mm"
include "dvdsmul1.mm"
include "sylancr.mm"
include "cc.mm"
include "zcn.mm"
include "2cn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "pnpcan2.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "subdi.mm"
include "mp3an1.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "oveq12.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "imp.mm"
include "an4s.mm"

theorem omoe
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( ( A e. ZZ /\ -. 2 || A ) /\ ( B e. ZZ /\ -. 2 || B ) ) -> 2 || ( A - B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    c2
    cA
    cdvds
    wbr
    wn
    #
    c2
    cB
    cdvds
    wbr
    wn
    #
    c2
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    @5
    @6
    @7
    c2
    va
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cA
    wceq
    #
    va
    cz
    wrex
    #
    c2
    vb
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cB
    wceq
    #
    vb
    cz
    wrex
    #
    wa
    #
    @5
    @0
    @2
    @12
    @1
    @3
    @17
    va
    cA
    odd2np1
    vb
    cB
    odd2np1
    bi2anan9
    @18
    @11
    @16
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    @5
    @11
    @16
    va
    vb
    cz
    cz
    reeanv
    @19
    @5
    va
    vb
    cz
    cz
    @8
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    wa
    #
    c2
    @10
    @15
    cmin
    co
    #
    cdvds
    wbr
    @19
    @5
    @22
    c2
    c2
    @8
    @13
    cmin
    co
    #
    cmul
    co
    #
    @23
    cdvds
    @22
    c2
    cz
    wcel
    @24
    cz
    wcel
    c2
    @25
    cdvds
    wbr
    2z
    @8
    @13
    zsubcl
    c2
    @24
    dvdsmul1
    sylancr
    @20
    @8
    cc
    wcel
    #
    @13
    cc
    wcel
    #
    @23
    @25
    wceq
    @21
    @8
    zcn
    @13
    zcn
    @26
    @27
    wa
    @23
    @9
    @14
    cmin
    co
    #
    @25
    @26
    @9
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @23
    @28
    wceq
    #
    @27
    c2
    cc
    wcel
    #
    @26
    @29
    2cn
    c2
    @8
    mulcl
    mpan
    @32
    @27
    @30
    2cn
    c2
    @13
    mulcl
    mpan
    @29
    @30
    c1
    cc
    wcel
    @31
    ax-1cn
    @9
    @14
    c1
    pnpcan2
    mp3an3
    syl2an
    @32
    @26
    @27
    @25
    @28
    wceq
    2cn
    c2
    @8
    @13
    subdi
    mp3an1
    eqtr4d
    syl2an
    breqtrrd
    @19
    @23
    @4
    c2
    cdvds
    @10
    cA
    @15
    cB
    cmin
    oveq12
    breq2d
    syl5ibcom
    rexlimivv
    sylbir
    syl6bi
    imp
    an4s
end
