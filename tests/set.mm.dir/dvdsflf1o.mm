include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cmul.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cle.mm"
include "elfznn.mm"
include "nnmulcl.mm"
include "syl2an.mm"
include "cr.mm"
include "wb.mm"
include "nndivred.mm"
include "fznnfl.mm"
include "syl.mm"
include "simplbda.mm"
include "cc0.mm"
include "clt.mm"
include "adantl.mm"
include "nnred.mm"
include "adantr.mm"
include "nngt0d.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "cz.mm"
include "nnzd.mm"
include "elfzelz.mm"
include "zmulcl.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "flcld.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "dvdsmul1.mm"
include "breq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "simprbi.mm"
include "elrabi.mm"
include "nndivdvds.mm"
include "sylan2.mm"
include "lediv1.mm"
include "wceq.mm"
include "cc.mm"
include "nncnd.mm"
include "adantrl.mm"
include "adantrr.mm"
include "wne.mm"
include "nnne0d.mm"
include "divmuld.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1o2d.mm"

theorem dvdsflf1o
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vm: setvar m
  assume dvdsflf1o.1: |- ( ph -> A e. RR )
  assume dvdsflf1o.2: |- ( ph -> N e. NN )
  assume dvdsflf1o.f: |- F = ( n e. ( 1 ... ( |_ ` ( A / N ) ) ) |-> ( N x. n ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> F : ( 1 ... ( |_ ` ( A / N ) ) ) -1-1-onto-> { x e. ( 1 ... ( |_ ` A ) ) | N || x } )

  proof
    wph
    vn
    vm
    c1
    cA
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cN
    vx
    cv
    #
    cdvds
    wbr
    #
    vx
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    crab
    #
    cN
    vn
    cv
    #
    cmul
    co
    #
    vm
    cv
    #
    cN
    cdiv
    co
    #
    cF
    dvdsflf1o.f
    wph
    @8
    @2
    wcel
    #
    wa
    #
    @9
    @6
    wcel
    #
    cN
    @9
    cdvds
    wbr
    #
    @9
    @7
    wcel
    @13
    @14
    @9
    cn
    wcel
    #
    @9
    @5
    cle
    wbr
    #
    wph
    cN
    cn
    wcel
    #
    @8
    cn
    wcel
    #
    @16
    @12
    dvdsflf1o.2
    @8
    @1
    elfznn
    #
    cN
    @8
    nnmulcl
    syl2an
    @13
    @9
    cA
    cle
    wbr
    #
    @17
    @13
    @21
    @8
    @0
    cle
    wbr
    #
    wph
    @12
    @19
    @22
    wph
    @0
    cr
    wcel
    #
    @12
    @19
    @22
    wa
    wb
    wph
    cA
    cN
    dvdsflf1o.1
    dvdsflf1o.2
    nndivred
    #
    @8
    @0
    fznnfl
    syl
    simplbda
    @13
    @8
    cr
    wcel
    cA
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    @21
    @22
    wb
    @13
    @8
    @12
    @19
    wph
    @20
    adantl
    #
    nnred
    wph
    @25
    @12
    dvdsflf1o.1
    adantr
    #
    wph
    @26
    @12
    wph
    cN
    dvdsflf1o.2
    nnred
    #
    adantr
    wph
    @27
    @12
    wph
    cN
    dvdsflf1o.2
    nngt0d
    #
    adantr
    @8
    cA
    cN
    lemuldiv2
    syl112anc
    mpbird
    @13
    @25
    @9
    cz
    wcel
    #
    @21
    @17
    wb
    @29
    wph
    cN
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @32
    @12
    wph
    cN
    dvdsflf1o.2
    nnzd
    #
    @8
    c1
    @1
    elfzelz
    #
    cN
    @8
    zmulcl
    syl2an
    cA
    @9
    flge
    syl2anc
    mpbid
    @13
    @5
    cz
    wcel
    #
    @14
    @16
    @17
    wa
    wb
    wph
    @37
    @12
    wph
    cA
    dvdsflf1o.1
    flcld
    adantr
    @9
    @5
    fznn
    syl
    mpbir2and
    wph
    @33
    @34
    @15
    @12
    @35
    @36
    cN
    @8
    dvdsmul1
    syl2an
    @4
    @15
    vx
    @9
    @6
    @3
    @9
    cN
    cdvds
    breq2
    elrab
    sylanbrc
    wph
    @10
    @7
    wcel
    #
    wa
    #
    @11
    @2
    wcel
    #
    @11
    cn
    wcel
    #
    @11
    @0
    cle
    wbr
    #
    @39
    cN
    @10
    cdvds
    wbr
    #
    @41
    @38
    @43
    wph
    @38
    @10
    @6
    wcel
    #
    @43
    @4
    @43
    vx
    @10
    @6
    @3
    @10
    cN
    cdvds
    breq2
    elrab
    simprbi
    adantl
    @39
    @10
    cn
    wcel
    #
    @18
    @43
    @41
    wb
    @39
    @44
    @45
    @38
    @44
    wph
    @4
    vx
    @10
    @6
    elrabi
    #
    adantl
    @10
    @5
    elfznn
    syl
    #
    wph
    @18
    @38
    dvdsflf1o.2
    adantr
    @10
    cN
    nndivdvds
    syl2anc
    mpbid
    @39
    @10
    cA
    cle
    wbr
    #
    @42
    @38
    wph
    @44
    @48
    @46
    wph
    @44
    @45
    @48
    wph
    @25
    @44
    @45
    @48
    wa
    wb
    dvdsflf1o.1
    @10
    cA
    fznnfl
    syl
    simplbda
    sylan2
    @39
    @10
    cr
    wcel
    @25
    @26
    @27
    @48
    @42
    wb
    @39
    @10
    @47
    nnred
    wph
    @25
    @38
    dvdsflf1o.1
    adantr
    wph
    @26
    @38
    @30
    adantr
    wph
    @27
    @38
    @31
    adantr
    @10
    cA
    cN
    lediv1
    syl112anc
    mpbid
    @39
    @23
    @40
    @41
    @42
    wa
    wb
    wph
    @23
    @38
    @24
    adantr
    @11
    @0
    fznnfl
    syl
    mpbir2and
    wph
    @12
    @38
    wa
    #
    wa
    #
    @11
    @8
    wceq
    @9
    @10
    wceq
    @8
    @11
    wceq
    @10
    @9
    wceq
    @50
    @10
    cN
    @8
    wph
    @38
    @10
    cc
    wcel
    @12
    @39
    @10
    @47
    nncnd
    adantrl
    wph
    cN
    cc
    wcel
    @49
    wph
    cN
    dvdsflf1o.2
    nncnd
    adantr
    wph
    @12
    @8
    cc
    wcel
    @38
    @13
    @8
    @28
    nncnd
    adantrr
    wph
    cN
    cc0
    wne
    @49
    wph
    cN
    dvdsflf1o.2
    nnne0d
    adantr
    divmuld
    @8
    @11
    eqcom
    @10
    @9
    eqcom
    3bitr4g
    f1o2d
end
