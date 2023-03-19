include "cv.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfz.mm"
include "wcel.mm"
include "ccsh.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "adantr.mm"
include "cn0.mm"
include "elfznn0.mm"
include "nn0addcl.mm"
include "syl2anr.mm"
include "elfz3nn0.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "cword.mm"
include "cz.mm"
include "adantl.mm"
include "elfzelz.mm"
include "2cshw.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "jca.mm"
include "exp41.mm"
include "com23.mm"
include "com24.mm"
include "imp.mm"
include "com12.mm"
include "sylbid.mm"
include "ancoms.mm"
include "impcom.mm"
include "oveq2.mm"
include "rspcev.mm"
include "syl6com.mm"
include "wn.mm"
include "cmin.mm"
include "clt.mm"
include "cn.mm"
include "w3a.mm"
include "elfz2.mm"
include "nn0z.mm"
include "zaddcl.mm"
include "ex.mm"
include "zsubcld.mm"
include "syl.mm"
include "3adant1.mm"
include "sylbi.mm"
include "mpan9.mm"
include "cr.mm"
include "nn0re.mm"
include "anim12i.mm"
include "simplr.mm"
include "readdcl.mm"
include "adantlr.mm"
include "ltnled.mm"
include "posdifd.mm"
include "biimpd.mm"
include "sylbird.mm"
include "3adant3.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnnn0d.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "le2add.mm"
include "syl2anc.mm"
include "nn0readdcl.mm"
include "lesubadd2d.mm"
include "sylibrd.mm"
include "expcomd.mm"
include "3impia.mm"
include "com13.mm"
include "syl5bi.mm"
include "3adant2.mm"
include "syl6bi.mm"
include "cshwsublen.mm"
include "eqtrd.mm"
include "pm2.61ian.mm"

theorem cshwcsh2id
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cV: class V
  assume cshwcsh2id.1: |- ( ph -> z e. Word V )
  assume cshwcsh2id.2: |- ( ph -> ( ( # ` y ) = ( # ` z ) /\ ( # ` x ) = ( # ` y ) ) )

  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint n x
  disjoint n z
  disjoint x z
  assert |- ( ph -> ( ( ( m e. ( 0 ... ( # ` y ) ) /\ x = ( y cyclShift m ) ) /\ ( k e. ( 0 ... ( # ` z ) ) /\ y = ( z cyclShift k ) ) ) -> E. n e. ( 0 ... ( # ` z ) ) x = ( z cyclShift n ) ) )

  proof
    vk
    cv
    #
    vm
    cv
    #
    caddc
    co
    #
    vz
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    wph
    @1
    cc0
    vy
    cv
    #
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    vx
    cv
    #
    @6
    @1
    ccsh
    co
    #
    wceq
    #
    wa
    #
    @0
    cc0
    @4
    cfz
    co
    #
    wcel
    #
    @6
    @3
    @0
    ccsh
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    @10
    @3
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    @14
    wrex
    #
    wi
    @19
    @5
    wph
    wa
    #
    @2
    @14
    wcel
    #
    @10
    @3
    @2
    ccsh
    co
    #
    wceq
    #
    wa
    #
    @23
    @18
    @13
    @24
    @28
    wi
    #
    @17
    @15
    @13
    @29
    wi
    @17
    @15
    wa
    @13
    @9
    @10
    @16
    @1
    ccsh
    co
    #
    wceq
    #
    wa
    #
    @29
    @17
    @13
    @32
    wb
    @15
    @17
    @12
    @31
    @9
    @17
    @11
    @30
    @10
    @6
    @16
    @1
    ccsh
    oveq1
    eqeq2d
    anbi2d
    #
    adantr
    @15
    @32
    @29
    wi
    @17
    @32
    @15
    @29
    @9
    @31
    @15
    @29
    wi
    @9
    @24
    @15
    @31
    @28
    @9
    @15
    @24
    @31
    @28
    wi
    @9
    @15
    @24
    @31
    @28
    @9
    @15
    wa
    #
    @24
    wa
    #
    @31
    wa
    @25
    @27
    @35
    @25
    @31
    @35
    @2
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    @5
    @25
    @34
    @36
    @24
    @15
    @0
    cn0
    wcel
    #
    @1
    cn0
    wcel
    #
    @36
    @9
    @0
    @4
    elfznn0
    @1
    @7
    elfznn0
    #
    @0
    @1
    nn0addcl
    syl2anr
    adantr
    @15
    @37
    @9
    @24
    @0
    @4
    elfz3nn0
    #
    ad2antlr
    @34
    @5
    wph
    simprl
    @2
    @4
    elfz2nn0
    syl3anbrc
    adantr
    @35
    @31
    @27
    @35
    @30
    @26
    @10
    @35
    @3
    cV
    cword
    wcel
    #
    @0
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @30
    @26
    wceq
    #
    @24
    @42
    @34
    wph
    @42
    @5
    cshwcsh2id.1
    adantl
    adantl
    @15
    @43
    @9
    @24
    @0
    cc0
    @4
    elfzelz
    #
    ad2antlr
    @34
    @44
    @24
    @9
    @44
    @15
    @1
    cc0
    @7
    elfzelz
    #
    adantr
    #
    adantr
    @0
    @1
    cV
    @3
    2cshw
    #
    syl3anc
    eqeq2d
    biimpa
    jca
    exp41
    com23
    com24
    imp
    com12
    adantl
    sylbid
    ancoms
    impcom
    @22
    @27
    vn
    @2
    @14
    @20
    @2
    wceq
    @21
    @26
    @10
    @20
    @2
    @3
    ccsh
    oveq2
    eqeq2d
    rspcev
    syl6com
    @19
    @5
    wn
    #
    wph
    wa
    #
    @2
    @4
    cmin
    co
    #
    @14
    wcel
    #
    @10
    @3
    @52
    ccsh
    co
    #
    wceq
    #
    wa
    #
    @23
    @18
    @13
    @51
    @56
    wi
    #
    @17
    @15
    @13
    @57
    wi
    @17
    @13
    @15
    @57
    @17
    @13
    @32
    @15
    @57
    wi
    #
    @33
    @9
    @31
    @58
    @9
    @51
    @15
    @31
    @56
    @9
    @15
    @51
    @31
    @56
    wi
    @9
    @15
    @51
    @31
    @56
    @34
    @51
    wa
    #
    @31
    wa
    @53
    @55
    @59
    @53
    @31
    @59
    @52
    cn0
    wcel
    @37
    @52
    @4
    cle
    wbr
    #
    @53
    @59
    @52
    @59
    @52
    cz
    wcel
    #
    cc0
    @52
    clt
    wbr
    #
    @52
    cn
    wcel
    @34
    @61
    @51
    @9
    @39
    @15
    @61
    @40
    @15
    cc0
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @43
    w3a
    #
    cc0
    @0
    cle
    wbr
    @0
    @4
    cle
    wbr
    #
    wa
    #
    wa
    @39
    @61
    wi
    #
    @0
    cc0
    @4
    elfz2
    @65
    @68
    @67
    @64
    @43
    @68
    @63
    @39
    @64
    @43
    wa
    #
    @61
    @39
    @44
    @69
    @61
    wi
    @1
    nn0z
    @44
    @69
    @61
    @44
    @69
    wa
    @2
    @4
    @69
    @44
    @2
    cz
    wcel
    #
    @43
    @44
    @70
    wi
    @64
    @43
    @44
    @70
    @0
    @1
    zaddcl
    #
    ex
    adantl
    impcom
    @44
    @64
    @43
    simprl
    zsubcld
    ex
    syl
    com12
    3adant1
    adantr
    sylbi
    mpan9
    adantr
    @51
    @34
    @62
    @50
    @34
    @62
    wi
    wph
    @34
    @50
    @62
    @9
    @39
    @15
    @50
    @62
    wi
    #
    @40
    @15
    @38
    @37
    @66
    w3a
    #
    @39
    @72
    wi
    #
    @0
    @4
    elfz2nn0
    #
    @38
    @37
    @74
    @66
    @38
    @37
    wa
    #
    @39
    @72
    @76
    @39
    wa
    #
    @0
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    #
    @1
    cr
    wcel
    #
    wa
    #
    @72
    @76
    @80
    @39
    @81
    @38
    @78
    @37
    @79
    @0
    nn0re
    #
    @4
    nn0re
    #
    anim12i
    @1
    nn0re
    #
    anim12i
    @82
    @50
    @4
    @2
    clt
    wbr
    #
    @62
    @82
    @4
    @2
    @78
    @79
    @81
    simplr
    #
    @78
    @81
    @2
    cr
    wcel
    #
    @79
    @0
    @1
    readdcl
    adantlr
    #
    ltnled
    @82
    @86
    @62
    @82
    @4
    @2
    @87
    @89
    posdifd
    biimpd
    sylbird
    syl
    ex
    3adant3
    sylbi
    mpan9
    com12
    adantr
    impcom
    @52
    elnnz
    sylanbrc
    nnnn0d
    @15
    @37
    @9
    @51
    @41
    ad2antlr
    @51
    @34
    @60
    wph
    @34
    @60
    wi
    #
    @50
    wph
    @7
    @4
    wceq
    #
    @10
    chash
    cfv
    @7
    wceq
    #
    wa
    @90
    cshwcsh2id.2
    @91
    @90
    @92
    @91
    @34
    @1
    @14
    wcel
    #
    @15
    wa
    @60
    @91
    @9
    @93
    @15
    @91
    @8
    @14
    @1
    @7
    @4
    cc0
    cfz
    oveq2
    eleq2d
    anbi1d
    @93
    @15
    @60
    @93
    @39
    @37
    @1
    @4
    cle
    wbr
    #
    w3a
    @15
    @60
    wi
    #
    @1
    @4
    elfz2nn0
    @39
    @94
    @95
    @37
    @15
    @73
    @39
    @94
    wa
    @60
    @75
    @39
    @94
    @73
    @60
    wi
    @73
    @94
    @39
    @60
    @38
    @37
    @66
    @94
    @39
    @60
    wi
    wi
    @76
    @39
    @94
    @66
    @60
    @76
    @39
    @94
    @66
    @60
    wi
    wi
    @77
    @66
    @94
    @60
    @77
    @66
    @94
    wa
    #
    @2
    @4
    @4
    caddc
    co
    cle
    wbr
    #
    @60
    @77
    @78
    @81
    wa
    @79
    @79
    wa
    #
    @96
    @97
    wi
    @76
    @78
    @39
    @81
    @38
    @78
    @37
    @83
    adantr
    @85
    anim12i
    @37
    @98
    @38
    @39
    @37
    @79
    @79
    @84
    @84
    jca
    ad2antlr
    @0
    @1
    @4
    @4
    le2add
    syl2anc
    @77
    @2
    @4
    @4
    @38
    @39
    @88
    @37
    @0
    @1
    nn0readdcl
    adantlr
    @37
    @79
    @38
    @39
    @84
    ad2antlr
    #
    @99
    lesubadd2d
    sylibrd
    expcomd
    ex
    com24
    3impia
    com13
    imp
    syl5bi
    3adant2
    sylbi
    imp
    syl6bi
    adantr
    syl
    adantl
    impcom
    @52
    @4
    elfz2nn0
    syl3anbrc
    adantr
    @59
    @31
    @55
    @59
    @30
    @54
    @10
    @59
    @30
    @26
    @54
    @59
    @42
    @43
    @44
    @45
    @51
    @42
    @34
    wph
    @42
    @50
    cshwcsh2id.1
    adantl
    #
    adantl
    @15
    @43
    @9
    @51
    @46
    ad2antlr
    @34
    @44
    @51
    @48
    adantr
    @49
    syl3anc
    @51
    @42
    @70
    @26
    @54
    wceq
    @34
    @100
    @15
    @43
    @44
    @70
    @9
    @46
    @47
    @71
    syl2anr
    @2
    cV
    @3
    cshwsublen
    syl2anr
    eqtrd
    eqeq2d
    biimpa
    jca
    exp41
    com23
    com24
    imp
    syl6bi
    com23
    impcom
    impcom
    @22
    @55
    vn
    @52
    @14
    @20
    @52
    wceq
    @21
    @54
    @10
    @20
    @52
    @3
    ccsh
    oveq2
    eqeq2d
    rspcev
    syl6com
    pm2.61ian
end
