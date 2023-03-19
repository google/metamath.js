include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "csb.mm"
include "csu.mm"
include "caddc.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wral.mm"
include "fznn0sub2.mm"
include "ad2antll.mm"
include "expr.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "adantrr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "rspc.mm"
include "sylc.mm"
include "fsum0diag.mm"
include "mpan9.mm"
include "csbeq1.mm"
include "fsumrev2.mm"
include "cn0.mm"
include "cz.mm"
include "elfz3nn0.mm"
include "ad2antlr.mm"
include "elfzelz.mm"
include "nn0cn.mm"
include "zcn.mm"
include "subcl.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "addid2.mm"
include "syl.mm"
include "oveq1d.mm"
include "csbeq1d.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "adantl.mm"
include "3syl.mm"
include "oveq2d.mm"
include "adantr.mm"
include "sub32.mm"
include "syl3an.mm"
include "syl3anc.mm"
include "sumeq12rdv.mm"
include "3eqtr4d.mm"
include "fzfid.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz3.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "wb.mm"
include "elfzel2.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "subid.mm"
include "eleqtrd.mm"
include "simpll.mm"
include "wss.mm"
include "fzss2.mm"
include "sselda.mm"
include "fsumcl.mm"
include "oveq2.mm"
include "oveq1.mm"
include "sumeq12dv.mm"
include "eqtr4d.mm"
include "vex.mm"
include "csbie.mm"
include "a1i.mm"
include "sumeq2i.mm"
include "ovex.mm"
include "3eqtr3g.mm"

theorem fsum0diag2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  assume fsum0diag2.1: |- ( x = k -> B = A )
  assume fsum0diag2.2: |- ( x = ( k - j ) -> B = C )
  assume fsum0diag2.3: |- ( ( ph /\ ( j e. ( 0 ... N ) /\ k e. ( 0 ... ( N - j ) ) ) ) -> A e. CC )

  disjoint j k
  disjoint j x
  disjoint N j
  disjoint k x
  disjoint N k
  disjoint N x
  disjoint j ph
  disjoint k ph
  disjoint B k
  disjoint A x
  disjoint C x
  disjoint j n
  disjoint k n
  disjoint n x
  disjoint N n
  disjoint n ph
  disjoint B n
  disjoint A n
  disjoint C n
  assert |- ( ph -> sum_ j e. ( 0 ... N ) sum_ k e. ( 0 ... ( N - j ) ) A = sum_ k e. ( 0 ... N ) sum_ j e. ( 0 ... k ) C )

  proof
    wph
    cc0
    cN
    cfz
    co
    #
    cc0
    cN
    vj
    cv
    #
    cmin
    co
    #
    cfz
    co
    #
    vx
    vk
    cv
    #
    cB
    csb
    #
    vk
    csu
    #
    vj
    csu
    #
    @0
    cc0
    @4
    cfz
    co
    #
    vx
    @4
    @1
    cmin
    co
    #
    cB
    csb
    #
    vj
    csu
    #
    vk
    csu
    #
    @0
    @3
    cA
    vk
    csu
    #
    vj
    csu
    @0
    @8
    cC
    vj
    csu
    #
    vk
    csu
    wph
    @7
    @0
    cc0
    cc0
    cN
    caddc
    co
    #
    vn
    cv
    #
    cmin
    co
    #
    cfz
    co
    #
    vx
    @17
    @1
    cmin
    co
    #
    cB
    csb
    #
    vj
    csu
    #
    vn
    csu
    #
    @12
    wph
    @0
    @3
    vx
    @2
    @16
    cmin
    co
    #
    cB
    csb
    #
    vn
    csu
    #
    vj
    csu
    @0
    cc0
    cN
    @16
    cmin
    co
    #
    cfz
    co
    #
    @24
    vj
    csu
    #
    vn
    csu
    @7
    @22
    wph
    @24
    vj
    vn
    cN
    wph
    @1
    @0
    wcel
    #
    @16
    @3
    wcel
    #
    wa
    wa
    @23
    @3
    wcel
    #
    cB
    cc
    wcel
    #
    vx
    @3
    wral
    #
    @24
    cc
    wcel
    #
    @30
    @31
    wph
    @29
    @16
    @2
    fznn0sub2
    ad2antll
    wph
    @29
    @33
    @30
    wph
    @29
    wa
    #
    cA
    cc
    wcel
    #
    vk
    @3
    wral
    @33
    @35
    @36
    vk
    @3
    wph
    @29
    @4
    @3
    wcel
    #
    @36
    fsum0diag2.3
    expr
    ralrimiv
    @32
    @36
    vx
    vk
    @3
    vx
    cv
    #
    @4
    wceq
    #
    cB
    cA
    cc
    fsum0diag2.1
    eleq1d
    cbvralv
    sylibr
    #
    adantrr
    @32
    @34
    vx
    @23
    @3
    vx
    @24
    cc
    vx
    @23
    cB
    nfcsb1v
    nfel1
    @38
    @23
    wceq
    cB
    @24
    cc
    vx
    @23
    cB
    csbeq1a
    eleq1d
    rspc
    sylc
    fsum0diag
    wph
    @0
    @6
    @25
    vj
    @35
    @6
    @3
    vx
    cc0
    @2
    caddc
    co
    #
    @16
    cmin
    co
    #
    cB
    csb
    #
    vn
    csu
    @25
    @35
    @5
    @43
    vk
    vn
    cc0
    @2
    @35
    @33
    @37
    @5
    cc
    wcel
    #
    @40
    @32
    @44
    vx
    @4
    @3
    vx
    @5
    cc
    vx
    @4
    cB
    nfcsb1v
    nfel1
    @39
    cB
    @5
    cc
    vx
    @4
    cB
    csbeq1a
    eleq1d
    rspc
    mpan9
    vx
    @4
    @42
    cB
    csbeq1
    fsumrev2
    @35
    @3
    @43
    @24
    vn
    @35
    @30
    wa
    #
    vx
    @42
    @23
    cB
    @45
    @41
    @2
    @16
    cmin
    @45
    @2
    cc
    wcel
    #
    @41
    @2
    wceq
    @45
    cN
    cn0
    wcel
    #
    @1
    cz
    wcel
    #
    @46
    @29
    @47
    wph
    @30
    @1
    cN
    elfz3nn0
    ad2antlr
    @29
    @48
    wph
    @30
    @1
    cc0
    cN
    elfzelz
    ad2antlr
    @47
    cN
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @46
    @48
    cN
    nn0cn
    #
    @1
    zcn
    #
    cN
    @1
    subcl
    syl2an
    syl2anc
    @2
    addid2
    syl
    oveq1d
    csbeq1d
    sumeq2dv
    eqtrd
    sumeq2dv
    wph
    @0
    @21
    @28
    vn
    wph
    @16
    @0
    wcel
    #
    wa
    #
    @18
    @27
    @20
    @24
    vj
    @54
    @17
    @26
    cc0
    cfz
    @54
    @15
    cN
    @16
    cmin
    @54
    @47
    @49
    @15
    cN
    wceq
    @53
    @47
    wph
    @16
    cN
    elfz3nn0
    #
    adantl
    @51
    cN
    addid2
    3syl
    oveq1d
    #
    oveq2d
    @54
    @1
    @27
    wcel
    #
    wa
    #
    vx
    @19
    @23
    cB
    @58
    @19
    @26
    @1
    cmin
    co
    #
    @23
    @54
    @19
    @59
    wceq
    @57
    @54
    @17
    @26
    @1
    cmin
    @56
    oveq1d
    adantr
    @58
    @47
    @16
    cz
    wcel
    #
    @48
    @59
    @23
    wceq
    #
    @53
    @47
    wph
    @57
    @55
    ad2antlr
    @53
    @60
    wph
    @57
    @16
    cc0
    cN
    elfzelz
    ad2antlr
    @57
    @48
    @54
    @1
    cc0
    @26
    elfzelz
    adantl
    @47
    @49
    @60
    @16
    cc
    wcel
    @48
    @50
    @61
    @51
    @16
    zcn
    @52
    cN
    @16
    @1
    sub32
    syl3an
    syl3anc
    eqtrd
    csbeq1d
    sumeq12rdv
    sumeq2dv
    3eqtr4d
    wph
    @11
    @21
    vk
    vn
    cc0
    cN
    wph
    @4
    @0
    wcel
    #
    wa
    #
    @8
    @10
    vj
    @63
    cc0
    @4
    fzfid
    @63
    @1
    @8
    wcel
    #
    wa
    #
    @9
    @3
    wcel
    @33
    @10
    cc
    wcel
    #
    @65
    @9
    @1
    @1
    cmin
    co
    #
    @2
    cfz
    co
    #
    @3
    @65
    @4
    @1
    cN
    cfz
    co
    wcel
    #
    @9
    @68
    wcel
    #
    @65
    @4
    @1
    cuz
    cfv
    wcel
    #
    cN
    @4
    cuz
    cfv
    wcel
    #
    @69
    @64
    @71
    @63
    @1
    cc0
    @4
    elfzuz3
    adantl
    @63
    @72
    @64
    @62
    @72
    wph
    @4
    cc0
    cN
    elfzuz3
    adantl
    #
    adantr
    @4
    @1
    cN
    elfzuzb
    sylanbrc
    @65
    @48
    cN
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @48
    @69
    @70
    wb
    @64
    @48
    @63
    @1
    cc0
    @4
    elfzelz
    adantl
    #
    @62
    @74
    wph
    @64
    @4
    cc0
    cN
    elfzel2
    ad2antlr
    @62
    @75
    wph
    @64
    @4
    cc0
    cN
    elfzelz
    ad2antlr
    @76
    @4
    @1
    @1
    cN
    fzsubel
    syl22anc
    mpbid
    @65
    @67
    cc0
    @2
    cfz
    @65
    @48
    @50
    @67
    cc0
    wceq
    @76
    @52
    @1
    subid
    3syl
    oveq1d
    eleqtrd
    @65
    wph
    @29
    @33
    wph
    @62
    @64
    simpll
    @63
    @8
    @0
    @1
    @63
    @72
    @8
    @0
    wss
    @73
    @4
    cc0
    cN
    fzss2
    syl
    sselda
    @40
    syl2anc
    @32
    @66
    vx
    @9
    @3
    vx
    @10
    cc
    vx
    @9
    cB
    nfcsb1v
    nfel1
    @38
    @9
    wceq
    cB
    @10
    cc
    vx
    @9
    cB
    csbeq1a
    eleq1d
    rspc
    sylc
    fsumcl
    @4
    @17
    wceq
    #
    @8
    @18
    @10
    @20
    vj
    @4
    @17
    cc0
    cfz
    oveq2
    @77
    @10
    @20
    wceq
    @64
    @77
    vx
    @9
    @19
    cB
    @4
    @17
    @1
    cmin
    oveq1
    csbeq1d
    adantr
    sumeq12dv
    fsumrev2
    eqtr4d
    @0
    @6
    @13
    vj
    @29
    @3
    @5
    cA
    vk
    @5
    cA
    wceq
    @29
    @37
    wa
    vx
    @4
    cB
    cA
    vk
    vex
    fsum0diag2.1
    csbie
    a1i
    sumeq2dv
    sumeq2i
    @0
    @11
    @14
    vk
    @62
    @8
    @10
    cC
    vj
    @10
    cC
    wceq
    @62
    @64
    wa
    vx
    @9
    cB
    cC
    @4
    @1
    cmin
    ovex
    fsum0diag2.2
    csbie
    a1i
    sumeq2dv
    sumeq2i
    3eqtr3g
end
