include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "csu.mm"
include "cdiv.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "wss.mm"
include "elfznn.mm"
include "adantl.mm"
include "dvdsssfz1.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cle.mm"
include "cr.mm"
include "nnre.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "nnred.mm"
include "ad2antrr.mm"
include "cz.mm"
include "wi.mm"
include "nnz.mm"
include "dvdsle.mm"
include "syl2anr.mm"
include "impr.mm"
include "wb.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "letrd.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "ancom.mm"
include "an32.mm"
include "bitri.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "an12.mm"
include "breq1.mm"
include "elrab.mm"
include "anbi2i.mm"
include "breq2.mm"
include "3bitr4g.mm"
include "fsumcom2.mm"
include "cmul.mm"
include "cmpt.mm"
include "simprbda.mm"
include "eqid.mm"
include "dvdsflf1o.mm"
include "wceq.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "cc.mm"
include "biimpar.mm"
include "syldan.mm"
include "anassrs.mm"
include "fsumf1o.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"

theorem dvdsflsumcom
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vd: setvar d
  let vy: setvar y
  assume dvdsflsumcom.1: |- ( n = ( d x. m ) -> B = C )
  assume dvdsflsumcom.2: |- ( ph -> A e. RR )
  assume dvdsflsumcom.3: |- ( ( ph /\ ( n e. ( 1 ... ( |_ ` A ) ) /\ d e. { x e. NN | x || n } ) ) -> B e. CC )

  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B m
  disjoint C n
  disjoint d ph
  disjoint m ph
  disjoint n ph
  disjoint d y
  disjoint m y
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( ph -> sum_ n e. ( 1 ... ( |_ ` A ) ) sum_ d e. { x e. NN | x || n } B = sum_ d e. ( 1 ... ( |_ ` A ) ) sum_ m e. ( 1 ... ( |_ ` ( A / d ) ) ) C )

  proof
    wph
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vx
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    cB
    vd
    csu
    vn
    csu
    @1
    vd
    cv
    #
    @2
    cdvds
    wbr
    #
    vx
    @1
    crab
    #
    cB
    vn
    csu
    #
    vd
    csu
    @1
    c1
    cA
    @6
    cdiv
    co
    cfl
    cfv
    #
    cfz
    co
    #
    cC
    vm
    csu
    #
    vd
    csu
    wph
    @1
    @5
    @1
    @8
    vn
    vd
    cB
    wph
    c1
    @0
    fzfid
    #
    @13
    wph
    @3
    @1
    wcel
    #
    wa
    #
    c1
    @3
    cfz
    co
    #
    cfn
    wcel
    @5
    @16
    wss
    #
    @5
    cfn
    wcel
    @15
    c1
    @3
    fzfid
    @15
    @3
    cn
    wcel
    #
    @17
    @14
    @18
    wph
    @3
    @0
    elfznn
    adantl
    #
    @3
    vx
    dvdsssfz1
    syl
    @16
    @5
    ssfi
    syl2anc
    wph
    @14
    @6
    cn
    wcel
    #
    @6
    @3
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @6
    @1
    wcel
    #
    @14
    @21
    wa
    #
    wa
    #
    @14
    @6
    @5
    wcel
    #
    wa
    #
    @24
    @3
    @8
    wcel
    #
    wa
    #
    wph
    @23
    @14
    @24
    @21
    wa
    #
    wa
    @26
    wph
    @14
    @22
    @31
    @15
    @22
    @20
    @6
    cA
    cle
    wbr
    #
    wa
    #
    @21
    wa
    #
    @31
    @15
    @22
    @32
    @22
    wa
    #
    @34
    @15
    @22
    @32
    @15
    @22
    @32
    @15
    @22
    wa
    #
    @6
    @3
    cA
    @20
    @6
    cr
    wcel
    @15
    @21
    @6
    nnre
    ad2antrl
    @36
    @3
    @15
    @18
    @22
    @19
    adantr
    nnred
    wph
    cA
    cr
    wcel
    #
    @14
    @22
    dvdsflsumcom.2
    ad2antrr
    @15
    @20
    @21
    @6
    @3
    cle
    wbr
    #
    @20
    @6
    cz
    wcel
    @18
    @21
    @38
    wi
    @15
    @6
    nnz
    @19
    @6
    @3
    dvdsle
    syl2anr
    impr
    @15
    @3
    cA
    cle
    wbr
    #
    @22
    wph
    @14
    @18
    @39
    wph
    @37
    @14
    @18
    @39
    wa
    wb
    dvdsflsumcom.2
    @3
    cA
    fznnfl
    syl
    simplbda
    adantr
    letrd
    ex
    pm4.71rd
    @35
    @22
    @32
    wa
    @34
    @32
    @22
    ancom
    @20
    @21
    @32
    an32
    bitri
    syl6bb
    @15
    @24
    @33
    @21
    wph
    @24
    @33
    wb
    #
    @14
    wph
    @37
    @40
    dvdsflsumcom.2
    @6
    cA
    fznnfl
    syl
    #
    adantr
    anbi1d
    bitr4d
    pm5.32da
    @14
    @24
    @21
    an12
    syl6bb
    @27
    @22
    @14
    @4
    @21
    vx
    @6
    cn
    @2
    @6
    @3
    cdvds
    breq1
    elrab
    anbi2i
    @29
    @25
    @24
    @7
    @21
    vx
    @3
    @1
    @2
    @3
    @6
    cdvds
    breq2
    elrab
    anbi2i
    3bitr4g
    #
    dvdsflsumcom.3
    fsumcom2
    wph
    @1
    @9
    @12
    vd
    wph
    @24
    wa
    #
    @8
    cB
    @11
    cC
    vn
    vm
    vy
    @11
    @6
    vy
    cv
    #
    cmul
    co
    #
    cmpt
    #
    @6
    vm
    cv
    #
    cmul
    co
    #
    dvdsflsumcom.1
    @43
    c1
    @10
    fzfid
    @43
    vx
    cA
    vy
    @46
    @6
    wph
    @37
    @24
    dvdsflsumcom.2
    adantr
    wph
    @24
    @20
    @32
    @41
    simprbda
    @46
    eqid
    #
    dvdsflf1o
    @47
    @11
    wcel
    @47
    @46
    cfv
    @48
    wceq
    @43
    vy
    @47
    @45
    @48
    @11
    @46
    @44
    @47
    @6
    cmul
    oveq2
    @49
    @6
    @47
    cmul
    ovex
    fvmpt
    adantl
    wph
    @24
    @29
    cB
    cc
    wcel
    #
    wph
    @30
    @28
    @50
    wph
    @28
    @30
    @42
    biimpar
    dvdsflsumcom.3
    syldan
    anassrs
    fsumf1o
    sumeq2dv
    eqtrd
end
