include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cmin.mm"
include "wb.mm"
include "2re.mm"
include "1re.mm"
include "ltsub1.mm"
include "mp3an13.mm"
include "2m1e1.mm"
include "breq1i.mm"
include "syl6bb.mm"
include "bi2anan9.mm"
include "wi.mm"
include "peano2rem.mm"
include "mulgt1.mm"
include "ex.mm"
include "syl2an.mm"
include "sylbid.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "ax-1cn.mm"
include "mulsub.mm"
include "mpanl2.mm"
include "mpanr2.mm"
include "breq2d.mm"
include "1t1e1.mm"
include "oveq2i.mm"
include "breq2i.mm"
include "remulcl.mm"
include "mpan2.mm"
include "readdcl.mm"
include "remulcli.mm"
include "sylancl.mm"
include "ltaddsub2.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "syl5rbbr.mm"
include "ltadd1.mm"
include "mp3an3.mm"
include "ax-1rid.mm"
include "oveqan12d.mm"
include "breq1d.mm"
include "bitr3d.mm"
include "3bitrd.mm"
include "sylibd.mm"
include "imp.mm"

theorem addltmul
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 2 < A /\ 2 < B ) ) -> ( A + B ) < ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    c2
    cA
    clt
    wbr
    #
    c2
    cB
    clt
    wbr
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @5
    c1
    cA
    c1
    cmin
    co
    #
    cB
    c1
    cmin
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    @8
    @2
    @5
    c1
    @9
    clt
    wbr
    #
    c1
    @10
    clt
    wbr
    #
    wa
    #
    @12
    @0
    @3
    @13
    @1
    @4
    @14
    @0
    @3
    c2
    c1
    cmin
    co
    #
    @9
    clt
    wbr
    #
    @13
    c2
    cr
    wcel
    #
    @0
    c1
    cr
    wcel
    #
    @3
    @17
    wb
    2re
    1re
    c2
    cA
    c1
    ltsub1
    mp3an13
    @16
    c1
    @9
    clt
    2m1e1
    breq1i
    syl6bb
    @1
    @4
    @16
    @10
    clt
    wbr
    #
    @14
    @18
    @1
    @19
    @4
    @20
    wb
    2re
    1re
    c2
    cB
    c1
    ltsub1
    mp3an13
    @16
    c1
    @10
    clt
    2m1e1
    breq1i
    syl6bb
    bi2anan9
    @0
    @9
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @15
    @12
    wi
    @1
    cA
    peano2rem
    cB
    peano2rem
    @21
    @22
    wa
    @15
    @12
    @9
    @10
    mulgt1
    ex
    syl2an
    sylbid
    @2
    @12
    c1
    @7
    c1
    c1
    cmul
    co
    #
    caddc
    co
    #
    cA
    c1
    cmul
    co
    #
    cB
    c1
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    clt
    wbr
    #
    @27
    c1
    caddc
    co
    #
    @7
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @8
    @2
    @11
    @28
    c1
    clt
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @11
    @28
    wceq
    #
    @1
    cA
    recn
    cB
    recn
    @33
    @34
    c1
    cc
    wcel
    #
    @35
    ax-1cn
    @33
    @36
    @34
    @36
    wa
    @35
    ax-1cn
    cA
    c1
    cB
    c1
    mulsub
    mpanl2
    mpanr2
    syl2an
    breq2d
    @32
    @30
    @24
    clt
    wbr
    #
    @2
    @29
    @24
    @31
    @30
    clt
    @23
    c1
    @7
    caddc
    1t1e1
    oveq2i
    breq2i
    @2
    @27
    cr
    wcel
    #
    @24
    cr
    wcel
    #
    @37
    @29
    wb
    #
    @0
    @25
    cr
    wcel
    #
    @26
    cr
    wcel
    #
    @38
    @1
    @0
    @19
    @41
    1re
    cA
    c1
    remulcl
    mpan2
    @1
    @19
    @42
    1re
    cB
    c1
    remulcl
    mpan2
    @25
    @26
    readdcl
    syl2an
    #
    @2
    @7
    cr
    wcel
    #
    @23
    cr
    wcel
    @39
    cA
    cB
    remulcl
    #
    c1
    c1
    1re
    1re
    remulcli
    @7
    @23
    readdcl
    sylancl
    @38
    @19
    @39
    @40
    1re
    @27
    c1
    @24
    ltaddsub2
    mp3an2
    syl2anc
    syl5rbbr
    @2
    @27
    @7
    clt
    wbr
    #
    @32
    @8
    @2
    @38
    @44
    @46
    @32
    wb
    #
    @43
    @45
    @38
    @44
    @19
    @47
    1re
    @27
    @7
    c1
    ltadd1
    mp3an3
    syl2anc
    @2
    @27
    @6
    @7
    clt
    @0
    @1
    @25
    cA
    @26
    cB
    caddc
    cA
    ax-1rid
    cB
    ax-1rid
    oveqan12d
    breq1d
    bitr3d
    3bitrd
    sylibd
    imp
end
