include "cv.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cdiv.mm"
include "wa.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "simprr.mm"
include "cr.mm"
include "wb.mm"
include "adantr.mm"
include "simprl.mm"
include "fznnfl.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "nndivred.mm"
include "nnred.mm"
include "simprd.mm"
include "cmul.mm"
include "recnd.mm"
include "mulid2d.mm"
include "nnge1d.mm"
include "cc0.mm"
include "clt.mm"
include "1red.mm"
include "0red.mm"
include "nnmulcld.mm"
include "nngt0d.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "ltletrd.mm"
include "lemul1.mm"
include "eqbrtrrd.mm"
include "ledivmul.mm"
include "letrd.mm"
include "mpbir2and.mm"
include "lemuldiv.mm"
include "jca.mm"
include "ex.mm"

theorem fsumfldivdiaglem
  let wph: wff ph
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  assume fsumfldivdiag.1: |- ( ph -> A e. RR )

  disjoint m n
  disjoint A m
  disjoint A n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( ( n e. ( 1 ... ( |_ ` A ) ) /\ m e. ( 1 ... ( |_ ` ( A / n ) ) ) ) -> ( m e. ( 1 ... ( |_ ` A ) ) /\ n e. ( 1 ... ( |_ ` ( A / m ) ) ) ) ) )

  proof
    wph
    vn
    cv
    #
    c1
    cA
    cfl
    cfv
    cfz
    co
    #
    wcel
    #
    vm
    cv
    #
    c1
    cA
    @0
    cdiv
    co
    #
    cfl
    cfv
    cfz
    co
    wcel
    #
    wa
    #
    @3
    @1
    wcel
    #
    @0
    c1
    cA
    @3
    cdiv
    co
    #
    cfl
    cfv
    cfz
    co
    wcel
    #
    wa
    wph
    @6
    wa
    #
    @7
    @9
    @10
    @7
    @3
    cn
    wcel
    #
    @3
    cA
    cle
    wbr
    #
    @10
    @11
    @3
    @4
    cle
    wbr
    #
    @10
    @5
    @11
    @13
    wa
    #
    wph
    @2
    @5
    simprr
    @10
    @4
    cr
    wcel
    @5
    @14
    wb
    @10
    cA
    @0
    wph
    cA
    cr
    wcel
    #
    @6
    fsumfldivdiag.1
    adantr
    #
    @10
    @0
    cn
    wcel
    #
    @0
    cA
    cle
    wbr
    #
    @10
    @2
    @17
    @18
    wa
    #
    wph
    @2
    @5
    simprl
    @10
    @15
    @2
    @19
    wb
    @16
    @0
    cA
    fznnfl
    syl
    mpbid
    simpld
    #
    nndivred
    #
    @3
    @4
    fznnfl
    syl
    mpbid
    #
    simpld
    #
    @10
    @3
    @4
    cA
    @10
    @3
    @23
    nnred
    #
    @21
    @16
    @10
    @11
    @13
    @22
    simprd
    #
    @10
    @4
    cA
    cle
    wbr
    #
    cA
    @0
    cA
    cmul
    co
    #
    cle
    wbr
    #
    @10
    c1
    cA
    cmul
    co
    #
    cA
    @27
    cle
    @10
    cA
    @10
    cA
    @16
    recnd
    mulid2d
    @10
    c1
    @0
    cle
    wbr
    #
    @29
    @27
    cle
    wbr
    #
    @10
    @0
    @20
    nnge1d
    @10
    c1
    cr
    wcel
    @0
    cr
    wcel
    #
    @15
    cc0
    cA
    clt
    wbr
    @30
    @31
    wb
    @10
    1red
    @10
    @0
    @20
    nnred
    #
    @16
    @10
    cc0
    @0
    @3
    cmul
    co
    #
    cA
    @10
    0red
    @10
    @34
    @10
    @0
    @3
    @20
    @23
    nnmulcld
    #
    nnred
    @16
    @10
    @34
    @35
    nngt0d
    @10
    @34
    cA
    cle
    wbr
    #
    @13
    @25
    @10
    @3
    cr
    wcel
    #
    @15
    @32
    cc0
    @0
    clt
    wbr
    #
    @36
    @13
    wb
    @24
    @16
    @33
    @10
    @0
    @20
    nngt0d
    #
    @3
    cA
    @0
    lemuldiv2
    syl112anc
    mpbird
    #
    ltletrd
    c1
    @0
    cA
    lemul1
    syl112anc
    mpbid
    eqbrtrrd
    @10
    @15
    @15
    @32
    @38
    @26
    @28
    wb
    @16
    @16
    @33
    @39
    cA
    cA
    @0
    ledivmul
    syl112anc
    mpbird
    letrd
    @10
    @15
    @7
    @11
    @12
    wa
    wb
    @16
    @3
    cA
    fznnfl
    syl
    mpbir2and
    @10
    @9
    @17
    @0
    @8
    cle
    wbr
    #
    @20
    @10
    @36
    @41
    @40
    @10
    @32
    @15
    @37
    cc0
    @3
    clt
    wbr
    @36
    @41
    wb
    @33
    @16
    @24
    @10
    @3
    @23
    nngt0d
    @0
    cA
    @3
    lemuldiv
    syl112anc
    mpbid
    @10
    @8
    cr
    wcel
    @9
    @17
    @41
    wa
    wb
    @10
    cA
    @3
    @16
    @23
    nndivred
    @0
    @8
    fznnfl
    syl
    mpbir2and
    jca
    ex
end
