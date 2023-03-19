include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "odd2np1.mm"
include "bi2anan9.mm"
include "reeanv.mm"
include "2z.mm"
include "zaddcl.mm"
include "peano2zd.mm"
include "dvdsmul1.mm"
include "sylancr.mm"
include "cc.mm"
include "zcn.mm"
include "addcl.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an13.mm"
include "syl.mm"
include "mp3an1.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "2t1e2.mm"
include "df-2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "mulcl.mm"
include "mpan.mm"
include "add4.mm"
include "mpanr12.mm"
include "syl2an.mm"
include "breqtrd.mm"
include "oveq12.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "imp.mm"
include "an4s.mm"

theorem opoe
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( ( A e. ZZ /\ -. 2 || A ) /\ ( B e. ZZ /\ -. 2 || B ) ) -> 2 || ( A + B ) )

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
    caddc
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
    caddc
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
    caddc
    co
    #
    c1
    caddc
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
    @25
    cz
    wcel
    c2
    @26
    cdvds
    wbr
    2z
    @22
    @24
    @8
    @13
    zaddcl
    peano2zd
    c2
    @25
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
    @26
    @23
    wceq
    @21
    @8
    zcn
    @13
    zcn
    @27
    @28
    wa
    #
    @26
    @9
    @14
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @23
    @29
    @26
    @30
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @32
    @29
    @26
    c2
    @24
    cmul
    co
    #
    @33
    caddc
    co
    #
    @34
    @29
    @24
    cc
    wcel
    #
    @26
    @36
    wceq
    #
    @8
    @13
    addcl
    c2
    cc
    wcel
    #
    @37
    c1
    cc
    wcel
    #
    @38
    2cn
    ax-1cn
    c2
    @24
    c1
    adddi
    mp3an13
    syl
    @29
    @35
    @30
    @33
    caddc
    @39
    @27
    @28
    @35
    @30
    wceq
    2cn
    c2
    @8
    @13
    adddi
    mp3an1
    oveq1d
    eqtrd
    @33
    @31
    @30
    caddc
    @33
    c2
    @31
    2t1e2
    df-2
    eqtri
    oveq2i
    syl6eq
    @27
    @9
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @32
    @23
    wceq
    #
    @28
    @39
    @27
    @41
    2cn
    c2
    @8
    mulcl
    mpan
    @39
    @28
    @42
    2cn
    c2
    @13
    mulcl
    mpan
    @41
    @42
    wa
    @40
    @40
    @43
    ax-1cn
    ax-1cn
    @9
    @14
    c1
    c1
    add4
    mpanr12
    syl2an
    eqtrd
    syl2an
    breqtrd
    @19
    @23
    @4
    c2
    cdvds
    @10
    cA
    @15
    cB
    caddc
    oveq12
    breq2d
    syl5ibcom
    rexlimivv
    sylbir
    syl6bi
    imp
    an4s
end
