include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "odd2np1.mm"
include "wb.mm"
include "2z.mm"
include "divides.mm"
include "mpan.mm"
include "bi2anan9.mm"
include "reeanv.mm"
include "zaddcl.mm"
include "cc.mm"
include "zcn.mm"
include "2cn.mm"
include "adddi.mm"
include "mp3an1.mm"
include "oveq1d.mm"
include "mulcl.mm"
include "ax-1cn.mm"
include "add32.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "mulcom.mm"
include "adantl.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "oveq12.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "imp.mm"
include "an4s.mm"
include "ad2ant2r.mm"
include "syl.mm"
include "mpbird.mm"

theorem opeo
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( ( A e. ZZ /\ -. 2 || A ) /\ ( B e. ZZ /\ 2 || B ) ) -> -. 2 || ( A + B ) )

  proof
    cA
    cz
    wcel
    #
    c2
    cA
    cdvds
    wbr
    wn
    #
    wa
    cB
    cz
    wcel
    #
    c2
    cB
    cdvds
    wbr
    #
    wa
    wa
    #
    c2
    cA
    cB
    caddc
    co
    #
    cdvds
    wbr
    wn
    #
    c2
    vc
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @5
    wceq
    #
    vc
    cz
    wrex
    #
    @0
    @2
    @1
    @3
    @11
    @0
    @2
    wa
    #
    @1
    @3
    wa
    #
    @11
    @12
    @13
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
    vb
    cv
    #
    c2
    cmul
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
    @11
    @0
    @1
    @18
    @2
    @3
    @22
    va
    cA
    odd2np1
    c2
    cz
    wcel
    @2
    @3
    @22
    wb
    2z
    vb
    c2
    cB
    divides
    mpan
    bi2anan9
    @23
    @17
    @21
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    @11
    @17
    @21
    va
    vb
    cz
    cz
    reeanv
    @24
    @11
    va
    vb
    cz
    cz
    @14
    cz
    wcel
    #
    @19
    cz
    wcel
    #
    wa
    #
    @9
    @16
    @20
    caddc
    co
    #
    wceq
    #
    vc
    cz
    wrex
    #
    @24
    @11
    @27
    @14
    @19
    caddc
    co
    #
    cz
    wcel
    c2
    @31
    cmul
    co
    #
    c1
    caddc
    co
    #
    @28
    wceq
    #
    @30
    @14
    @19
    zaddcl
    @25
    @14
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    @34
    @26
    @14
    zcn
    @19
    zcn
    @35
    @36
    wa
    #
    @33
    @15
    c2
    @19
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @16
    @38
    caddc
    co
    #
    @28
    @37
    @32
    @39
    c1
    caddc
    c2
    cc
    wcel
    #
    @35
    @36
    @32
    @39
    wceq
    2cn
    c2
    @14
    @19
    adddi
    mp3an1
    oveq1d
    @35
    @15
    cc
    wcel
    #
    @38
    cc
    wcel
    #
    @40
    @41
    wceq
    #
    @36
    @42
    @35
    @43
    2cn
    c2
    @14
    mulcl
    mpan
    @42
    @36
    @44
    2cn
    c2
    @19
    mulcl
    mpan
    @43
    @44
    c1
    cc
    wcel
    @45
    ax-1cn
    @15
    @38
    c1
    add32
    mp3an3
    syl2an
    @37
    @38
    @20
    @16
    caddc
    @36
    @38
    @20
    wceq
    #
    @35
    @42
    @36
    @46
    2cn
    c2
    @19
    mulcom
    mpan
    adantl
    oveq2d
    3eqtrd
    syl2an
    @29
    @34
    vc
    @31
    cz
    @7
    @31
    wceq
    #
    @9
    @33
    @28
    @47
    @8
    @32
    c1
    caddc
    @7
    @31
    c2
    cmul
    oveq2
    oveq1d
    eqeq1d
    rspcev
    syl2anc
    @24
    @29
    @10
    vc
    cz
    @24
    @28
    @5
    @9
    @16
    cA
    @20
    cB
    caddc
    oveq12
    eqeq2d
    rexbidv
    syl5ibcom
    rexlimivv
    sylbir
    syl6bi
    imp
    an4s
    @4
    @5
    cz
    wcel
    #
    @6
    @11
    wb
    @0
    @2
    @48
    @1
    @3
    cA
    cB
    zaddcl
    ad2ant2r
    vc
    @5
    odd2np1
    syl
    mpbird
end
