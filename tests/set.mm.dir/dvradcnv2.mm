include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cc0.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "cli.mm"
include "cdm.mm"
include "wceq.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "subnegi.mm"
include "0p1e1.mm"
include "eqtri.mm"
include "seqeq1.mm"
include "ax-mp.mm"
include "cshi.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "cmul.mm"
include "cexp.mm"
include "cmpt.mm"
include "cn.mm"
include "ovex.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "nnuz.mm"
include "cuz.mm"
include "nn0uz.mm"
include "1pneg1e0.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "1zzd.mm"
include "znegcld.mm"
include "uzmptshftfval.mm"
include "wa.mm"
include "cc.mm"
include "nn0cn.mm"
include "adantl.mm"
include "1cnd.mm"
include "subnegd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "seqeq3d.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "eqid.mm"
include "dvradcnv.mm"
include "eqeltrd.mm"
include "climdm.mm"
include "sylib.mm"
include "cz.mm"
include "0z.mm"
include "neg1z.mm"
include "cvv.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "seqshft.mm"
include "mp2an.mm"
include "breq1i.mm"
include "wb.mm"
include "seqex.mm"
include "climshft.mm"
include "bitri.mm"
include "fvex.mm"
include "breldm.mm"
include "sylbi.mm"
include "syl.mm"
include "syl5eqelr.mm"

theorem dvradcnv2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cX: class X
  let vr: setvar r
  let vm: setvar m
  assume dvradcnv2.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume dvradcnv2.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume dvradcnv2.h: |- H = ( n e. NN |-> ( ( n x. ( A ` n ) ) x. ( X ^ ( n - 1 ) ) ) )
  assume dvradcnv2.a: |- ( ph -> A : NN0 --> CC )
  assume dvradcnv2.x: |- ( ph -> X e. CC )
  assume dvradcnv2.l: |- ( ph -> ( abs ` X ) < R )

  disjoint r x
  disjoint X r
  disjoint X x
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint X n
  disjoint G r
  disjoint m r
  disjoint m x
  disjoint X m
  disjoint m n
  disjoint A m
  disjoint m ph
  disjoint H m
  assert |- ( ph -> seq 1 ( + , H ) e. dom ~~> )

  proof
    wph
    caddc
    cH
    c1
    cseq
    #
    caddc
    cH
    cc0
    c1
    cneg
    #
    cmin
    co
    #
    cseq
    #
    cli
    cdm
    #
    @2
    c1
    wceq
    @3
    @0
    wceq
    @2
    cc0
    c1
    caddc
    co
    c1
    cc0
    c1
    0cn
    ax-1cn
    subnegi
    0p1e1
    eqtri
    caddc
    cH
    @2
    c1
    seqeq1
    ax-mp
    wph
    caddc
    cH
    @1
    cshi
    co
    #
    cc0
    cseq
    #
    @6
    cli
    cfv
    #
    cli
    wbr
    #
    @3
    @4
    wcel
    #
    wph
    @6
    @4
    wcel
    @8
    wph
    @6
    caddc
    vm
    cn0
    vm
    cv
    #
    c1
    caddc
    co
    #
    @11
    cA
    cfv
    #
    cmul
    co
    #
    cX
    @10
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    @4
    wph
    @5
    @16
    caddc
    cc0
    wph
    @5
    vm
    cn0
    @10
    @1
    cmin
    co
    #
    @17
    cA
    cfv
    #
    cmul
    co
    #
    cX
    @17
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    @16
    wph
    vn
    vm
    vn
    cv
    #
    @23
    cA
    cfv
    #
    cmul
    co
    #
    cX
    @23
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @22
    cH
    c1
    @1
    cn0
    cn
    dvradcnv2.h
    @25
    @27
    cmul
    ovex
    @23
    @17
    wceq
    #
    @25
    @19
    @27
    @21
    cmul
    @29
    @23
    @17
    @24
    @18
    cmul
    @29
    id
    @23
    @17
    cA
    fveq2
    oveq12d
    @29
    @26
    @20
    cX
    cexp
    @23
    @17
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    nnuz
    cn0
    cc0
    cuz
    cfv
    c1
    @1
    caddc
    co
    #
    cuz
    cfv
    nn0uz
    @30
    cc0
    cuz
    1pneg1e0
    fveq2i
    eqtr4i
    wph
    1zzd
    #
    wph
    c1
    @31
    znegcld
    uzmptshftfval
    wph
    vm
    cn0
    @22
    @15
    wph
    @10
    cn0
    wcel
    #
    wa
    #
    @19
    @13
    @21
    @14
    cmul
    @33
    @17
    @11
    @18
    @12
    cmul
    @33
    @10
    c1
    @32
    @10
    cc
    wcel
    wph
    @10
    nn0cn
    adantl
    #
    @33
    1cnd
    #
    subnegd
    #
    @33
    @17
    @11
    cA
    @36
    fveq2d
    oveq12d
    @33
    @20
    @10
    cX
    cexp
    @33
    @20
    @11
    c1
    cmin
    co
    @10
    @33
    @17
    @11
    c1
    cmin
    @36
    oveq1d
    @33
    @10
    c1
    @34
    @35
    pncand
    eqtrd
    oveq2d
    oveq12d
    mpteq2dva
    eqtrd
    seqeq3d
    wph
    vx
    cA
    cR
    vm
    cG
    @16
    cX
    vr
    cG
    vx
    cc
    vn
    cn0
    @24
    vx
    cv
    #
    @23
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    vx
    cc
    vm
    cn0
    @10
    cA
    cfv
    #
    @37
    @10
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    dvradcnv2.g
    vx
    cc
    @40
    @44
    vn
    vm
    cn0
    @39
    @43
    @23
    @10
    wceq
    @24
    @41
    @38
    @42
    cmul
    @23
    @10
    cA
    fveq2
    @23
    @10
    @37
    cexp
    oveq2
    oveq12d
    cbvmptv
    mpteq2i
    eqtri
    dvradcnv2.r
    @16
    eqid
    dvradcnv2.a
    dvradcnv2.x
    dvradcnv2.l
    dvradcnv
    eqeltrd
    @6
    climdm
    sylib
    @8
    @3
    @7
    cli
    wbr
    #
    @9
    @8
    @3
    @1
    cshi
    co
    #
    @7
    cli
    wbr
    #
    @45
    @6
    @46
    @7
    cli
    cc0
    cz
    wcel
    @1
    cz
    wcel
    #
    @6
    @46
    wceq
    0z
    neg1z
    caddc
    cH
    cc0
    @1
    cH
    vn
    cn
    @28
    cmpt
    cvv
    dvradcnv2.h
    vn
    cn
    @28
    nnex
    mptex
    eqeltri
    seqshft
    mp2an
    breq1i
    @48
    @3
    cvv
    wcel
    @47
    @45
    wb
    neg1z
    caddc
    cH
    @2
    seqex
    #
    @7
    @3
    @1
    cvv
    climshft
    mp2an
    bitri
    @3
    @7
    cli
    @49
    @6
    cli
    fvex
    breldm
    sylbi
    syl
    syl5eqelr
end
