include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cfa.mm"
include "clog.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "cvma.mm"
include "cdiv.mm"
include "cmul.mm"
include "cn0.mm"
include "wceq.mm"
include "flge0nn0.mm"
include "logfac.mm"
include "syl.mm"
include "cdvds.mm"
include "crab.mm"
include "cn.mm"
include "fzfid.mm"
include "cfn.mm"
include "wss.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cz.mm"
include "wb.mm"
include "flcl.mm"
include "adantr.mm"
include "fznn.mm"
include "anbi1d.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "elfznn.mm"
include "ad2antrl.mm"
include "nnred.mm"
include "reflcl.mm"
include "ad3antrrr.mm"
include "simprr.mm"
include "wi.mm"
include "nnz.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "elfzle2.mm"
include "letrd.mm"
include "expl.mm"
include "pm4.71rd.mm"
include "an12.mm"
include "anass.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "bitr4d.mm"
include "breq2.mm"
include "elrab.mm"
include "anbi2i.mm"
include "breq1.mm"
include "cc.mm"
include "adantl.mm"
include "vmacl.mm"
include "recnd.mm"
include "adantrr.mm"
include "fsumcom2.mm"
include "chash.mm"
include "fsumconst.mm"
include "cen.mm"
include "cmpt.mm"
include "wf1o.mm"
include "simpll.mm"
include "eqid.mm"
include "dvdsflf1o.mm"
include "f1oeng.mm"
include "hasheni.mm"
include "simpl.mm"
include "nndivre.mm"
include "syl2an.mm"
include "clt.mm"
include "nngt0.mm"
include "jca.mm"
include "divge0.mm"
include "sylan2.mm"
include "hashfz1.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "flcld.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "sumeq2dv.mm"
include "vmasum.mm"
include "3eqtr3d.mm"
include "eqtr4d.mm"

theorem logfac2
  let cA: class A
  let vk: setvar k
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x

  disjoint A k
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d p
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint A x
  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( log ` ( ! ` ( |_ ` A ) ) ) = sum_ k e. ( 1 ... ( |_ ` A ) ) ( ( Lam ` k ) x. ( |_ ` ( A / k ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    cfl
    cfv
    #
    cfa
    cfv
    clog
    cfv
    #
    c1
    @3
    cfz
    co
    #
    vn
    cv
    #
    clog
    cfv
    #
    vn
    csu
    #
    @5
    vk
    cv
    #
    cvma
    cfv
    #
    cA
    @9
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    @2
    @3
    cn0
    wcel
    @4
    @8
    wceq
    cA
    flge0nn0
    vn
    @3
    logfac
    syl
    @2
    @5
    @9
    vx
    cv
    #
    cdvds
    wbr
    #
    vx
    @5
    crab
    #
    @10
    vn
    csu
    #
    vk
    csu
    @5
    @15
    @6
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @10
    vk
    csu
    #
    vn
    csu
    @14
    @8
    @2
    @5
    @17
    @5
    @20
    vk
    vn
    @10
    @2
    c1
    @3
    fzfid
    #
    @22
    @2
    @9
    @5
    wcel
    #
    wa
    #
    @5
    cfn
    wcel
    @17
    @5
    wss
    @17
    cfn
    wcel
    #
    @24
    c1
    @3
    fzfid
    @16
    vx
    @5
    ssrab2
    @5
    @17
    ssfi
    sylancl
    #
    @2
    @23
    @6
    @5
    wcel
    #
    @9
    @6
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @27
    @9
    cn
    wcel
    #
    @28
    wa
    #
    wa
    #
    @23
    @6
    @17
    wcel
    #
    wa
    @27
    @9
    @20
    wcel
    #
    wa
    @2
    @30
    @31
    @9
    @3
    cle
    wbr
    #
    wa
    #
    @29
    wa
    #
    @33
    @2
    @23
    @37
    @29
    @2
    @3
    cz
    wcel
    #
    @23
    @37
    wb
    @0
    @39
    @1
    cA
    flcl
    adantr
    @9
    @3
    fznn
    syl
    anbi1d
    @2
    @31
    @29
    wa
    #
    @36
    @40
    wa
    #
    @33
    @38
    @2
    @40
    @36
    @2
    @31
    @29
    @36
    @2
    @31
    wa
    #
    @29
    wa
    #
    @9
    @6
    @3
    @31
    @9
    cr
    wcel
    #
    @2
    @29
    @9
    nnre
    #
    ad2antlr
    @43
    @6
    @27
    @6
    cn
    wcel
    #
    @42
    @28
    @6
    @3
    elfznn
    #
    ad2antrl
    #
    nnred
    @0
    @3
    cr
    wcel
    @1
    @31
    @29
    cA
    reflcl
    ad3antrrr
    @43
    @28
    @9
    @6
    cle
    wbr
    #
    @42
    @27
    @28
    simprr
    @43
    @9
    cz
    wcel
    #
    @46
    @28
    @49
    wi
    @31
    @50
    @2
    @29
    @9
    nnz
    ad2antlr
    @48
    @9
    @6
    dvdsle
    syl2anc
    mpd
    @27
    @6
    @3
    cle
    wbr
    @42
    @28
    @6
    c1
    @3
    elfzle2
    ad2antrl
    letrd
    expl
    pm4.71rd
    @27
    @31
    @28
    an12
    @38
    @31
    @36
    @29
    wa
    wa
    @41
    @31
    @36
    @29
    anass
    @31
    @36
    @29
    an12
    bitri
    3bitr4g
    bitr4d
    @34
    @29
    @23
    @16
    @28
    vx
    @6
    @5
    @15
    @6
    @9
    cdvds
    breq2
    elrab
    anbi2i
    @35
    @32
    @27
    @19
    @28
    vx
    @9
    cn
    @15
    @9
    @6
    cdvds
    breq1
    elrab
    anbi2i
    3bitr4g
    @2
    @23
    @10
    cc
    wcel
    #
    @34
    @24
    @10
    @24
    @31
    @10
    cr
    wcel
    @23
    @31
    @2
    @9
    @3
    elfznn
    #
    adantl
    #
    @9
    vmacl
    syl
    recnd
    #
    adantrr
    fsumcom2
    @2
    @5
    @18
    @13
    vk
    @24
    @18
    @17
    chash
    cfv
    #
    @10
    cmul
    co
    #
    @12
    @10
    cmul
    co
    @13
    @24
    @25
    @51
    @18
    @56
    wceq
    @26
    @54
    @17
    @10
    vn
    fsumconst
    syl2anc
    @24
    @55
    @12
    @10
    cmul
    @24
    c1
    @12
    cfz
    co
    #
    chash
    cfv
    #
    @55
    @12
    @24
    @57
    @17
    cen
    wbr
    #
    @58
    @55
    wceq
    @24
    @57
    cfn
    wcel
    @57
    @17
    vm
    @57
    @9
    vm
    cv
    cmul
    co
    cmpt
    #
    wf1o
    @59
    @24
    c1
    @12
    fzfid
    @24
    vx
    cA
    vm
    @60
    @9
    @0
    @1
    @23
    simpll
    @53
    @60
    eqid
    dvdsflf1o
    @57
    @17
    cfn
    @60
    f1oeng
    syl2anc
    @57
    @17
    hasheni
    syl
    @24
    @12
    cn0
    wcel
    #
    @58
    @12
    wceq
    @24
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    @61
    @2
    @0
    @31
    @62
    @23
    @0
    @1
    simpl
    @52
    cA
    @9
    nndivre
    syl2an
    #
    @23
    @2
    @44
    cc0
    @9
    clt
    wbr
    #
    wa
    #
    @63
    @23
    @31
    @66
    @52
    @31
    @44
    @65
    @45
    @9
    nngt0
    jca
    syl
    cA
    @9
    divge0
    sylan2
    @11
    flge0nn0
    syl2anc
    @12
    hashfz1
    syl
    eqtr3d
    oveq1d
    @24
    @12
    @10
    @24
    @12
    @24
    @11
    @64
    flcld
    zcnd
    @54
    mulcomd
    3eqtrd
    sumeq2dv
    @2
    @5
    @21
    @7
    vn
    @2
    @27
    wa
    @46
    @21
    @7
    wceq
    @27
    @46
    @2
    @47
    adantl
    vx
    @6
    vk
    vmasum
    syl
    sumeq2dv
    3eqtr3d
    eqtr4d
end
