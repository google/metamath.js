include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfov.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfif.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "ibllem.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "eqidd.mm"
include "dmmptd.mm"
include "isibl.mm"

theorem isibl2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vy: setvar y
  let cF: class F
  assume isibl.1: |- ( ph -> G = ( x e. RR |-> if ( ( x e. A /\ 0 <_ T ) , T , 0 ) ) )
  assume isibl.2: |- ( ( ph /\ x e. A ) -> T = ( Re ` ( B / ( _i ^ k ) ) ) )
  assume isibl2.3: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint k ph
  disjoint ph x
  disjoint V x
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F f
  disjoint F k
  disjoint F x
  disjoint ph y
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> B ) e. MblFn /\ A. k e. ( 0 ... 3 ) ( S.2 ` G ) e. RR ) ) )

  proof
    wph
    vy
    cA
    vy
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    @2
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
    vk
    @1
    cG
    wph
    cG
    vx
    cr
    vx
    cv
    #
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
    #
    vy
    cr
    @0
    cA
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    @5
    cc0
    cif
    #
    cmpt
    #
    isibl.1
    wph
    @14
    vx
    cr
    @7
    cc0
    @6
    @1
    cfv
    #
    @3
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
    @17
    cc0
    cif
    #
    cmpt
    @9
    vy
    vx
    cr
    @13
    @20
    @12
    vx
    @5
    cc0
    @10
    @11
    vx
    @10
    vx
    nfv
    vx
    cc0
    @5
    cle
    vx
    cc0
    nfcv
    #
    vx
    cle
    nfcv
    vx
    @4
    cre
    vx
    cre
    nfcv
    vx
    @2
    @3
    cdiv
    vx
    cA
    cB
    @0
    nffvmpt1
    vx
    cdiv
    nfcv
    vx
    @3
    nfcv
    nfov
    nffv
    #
    nfbr
    nfan
    @22
    @21
    nfif
    vy
    @20
    nfcv
    @0
    @6
    wceq
    #
    @12
    @19
    @5
    @17
    cc0
    @23
    @10
    @7
    @11
    @18
    @0
    @6
    cA
    eleq1
    @23
    @5
    @17
    cc0
    cle
    @23
    @4
    @16
    cre
    @23
    @2
    @15
    @3
    cdiv
    @0
    @6
    @1
    fveq2
    oveq1d
    fveq2d
    #
    breq2d
    anbi12d
    @24
    ifbieq1d
    cbvmpt
    wph
    vx
    cr
    @20
    @8
    wph
    vx
    cA
    @17
    cT
    wph
    @7
    wa
    #
    @17
    cB
    @3
    cdiv
    co
    #
    cre
    cfv
    cT
    @25
    @16
    @26
    cre
    @25
    @15
    cB
    @3
    cdiv
    @25
    @7
    cB
    cV
    wcel
    @15
    cB
    wceq
    wph
    @7
    simpr
    isibl2.3
    vx
    cA
    cB
    cV
    @1
    @1
    eqid
    #
    fvmpt2
    syl2anc
    oveq1d
    fveq2d
    isibl.2
    eqtr4d
    ibllem
    mpteq2dv
    syl5eq
    eqtr4d
    wph
    @10
    wa
    #
    @5
    eqidd
    wph
    vx
    @1
    cA
    cB
    cV
    @27
    isibl2.3
    dmmptd
    @28
    @2
    eqidd
    isibl
end
