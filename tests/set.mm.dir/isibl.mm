include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cdm.mm"
include "cc0.mm"
include "cfv.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "csb.mm"
include "wceq.mm"
include "fvex.mm"
include "breq2.mm"
include "anbi2d.mm"
include "id.mm"
include "ifbieq1d.mm"
include "csbie.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "df-ibl.mm"
include "elrab2.mm"
include "anbi1d.mm"
include "ifbid.mm"
include "eqtr4d.mm"
include "ibllem.mm"
include "eqtrd.mm"
include "syl5bb.mm"

theorem isibl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vy: setvar y
  let cV: class V
  assume isibl.1: |- ( ph -> G = ( x e. RR |-> if ( ( x e. A /\ 0 <_ T ) , T , 0 ) ) )
  assume isibl.2: |- ( ( ph /\ x e. A ) -> T = ( Re ` ( B / ( _i ^ k ) ) ) )
  assume isibl.3: |- ( ph -> dom F = A )
  assume isibl.4: |- ( ( ph /\ x e. A ) -> ( F ` x ) = B )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint F k
  disjoint F x
  disjoint k ph
  disjoint ph x
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F f
  disjoint ph y
  disjoint V x
  assert |- ( ph -> ( F e. L^1 <-> ( F e. MblFn /\ A. k e. ( 0 ... 3 ) ( S.2 ` G ) e. RR ) ) )

  proof
    cF
    cibl
    wcel
    cF
    cmbf
    wcel
    #
    vx
    cr
    vx
    cv
    #
    cF
    cdm
    #
    wcel
    #
    cc0
    @1
    cF
    cfv
    #
    ci
    vk
    cv
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vk
    cc0
    c3
    cfz
    co
    #
    wral
    #
    wa
    wph
    @0
    cG
    citg2
    cfv
    #
    cr
    wcel
    #
    vk
    @14
    wral
    #
    wa
    vx
    cr
    vy
    @1
    vf
    cv
    #
    cfv
    #
    @5
    cdiv
    co
    #
    cre
    cfv
    #
    @1
    @19
    cdm
    #
    wcel
    #
    cc0
    vy
    cv
    #
    cle
    wbr
    #
    wa
    #
    @25
    cc0
    cif
    #
    csb
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vk
    @14
    wral
    @15
    vf
    cF
    cmbf
    cibl
    @19
    cF
    wceq
    #
    @32
    @13
    vk
    @14
    @33
    @31
    @12
    cr
    @33
    @30
    @11
    citg2
    @33
    vx
    cr
    @29
    @10
    @33
    @29
    @24
    cc0
    @22
    cle
    wbr
    #
    wa
    #
    @22
    cc0
    cif
    #
    @10
    vy
    @22
    @28
    @36
    @21
    cre
    fvex
    @25
    @22
    wceq
    #
    @27
    @35
    @25
    @22
    cc0
    @37
    @26
    @34
    @24
    @25
    @22
    cc0
    cle
    breq2
    anbi2d
    @37
    id
    ifbieq1d
    csbie
    @33
    @35
    @9
    @22
    @7
    cc0
    @33
    @24
    @3
    @34
    @8
    @33
    @23
    @2
    @1
    @19
    cF
    dmeq
    eleq2d
    @33
    @22
    @7
    cc0
    cle
    @33
    @21
    @6
    cre
    @33
    @20
    @4
    @5
    cdiv
    @1
    @19
    cF
    fveq1
    oveq1d
    fveq2d
    #
    breq2d
    anbi12d
    @38
    ifbieq1d
    syl5eq
    mpteq2dv
    fveq2d
    eleq1d
    ralbidv
    vx
    vy
    vf
    vk
    df-ibl
    elrab2
    wph
    @15
    @18
    @0
    wph
    @13
    @17
    vk
    @14
    wph
    @12
    @16
    cr
    wph
    @11
    cG
    citg2
    wph
    @11
    vx
    cr
    @1
    cA
    wcel
    #
    cc0
    cT
    cle
    wbr
    wa
    cT
    cc0
    cif
    #
    cmpt
    cG
    wph
    vx
    cr
    @10
    @40
    wph
    @10
    @39
    @8
    wa
    #
    @7
    cc0
    cif
    @40
    wph
    @9
    @41
    @7
    cc0
    wph
    @3
    @39
    @8
    wph
    @2
    cA
    @1
    isibl.3
    eleq2d
    anbi1d
    ifbid
    wph
    vx
    cA
    @7
    cT
    wph
    @39
    wa
    #
    @7
    cB
    @5
    cdiv
    co
    #
    cre
    cfv
    cT
    @42
    @6
    @43
    cre
    @42
    @4
    cB
    @5
    cdiv
    isibl.4
    oveq1d
    fveq2d
    isibl.2
    eqtr4d
    ibllem
    eqtrd
    mpteq2dv
    isibl.1
    eqtr4d
    fveq2d
    eleq1d
    ralbidv
    anbi2d
    syl5bb
end
