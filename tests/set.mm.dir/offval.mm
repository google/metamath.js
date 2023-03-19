include "cof.mm"
include "co.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wfn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "fndm.mm"
include "syl.mm"
include "ineq12d.mm"
include "syl6eq.mm"
include "mpteq1d.mm"
include "inex1g.mm"
include "syl5eqelr.mm"
include "mptexg.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "wa.mm"
include "dmeq.mm"
include "ineqan12d.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq12dv.mm"
include "df-of.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "eleq2i.mm"
include "elin.mm"
include "bitr3i.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "sylan2b.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"

theorem offval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let cX: class X
  assume offval.1: |- ( ph -> F Fn A )
  assume offval.2: |- ( ph -> G Fn B )
  assume offval.3: |- ( ph -> A e. V )
  assume offval.4: |- ( ph -> B e. W )
  assume offval.5: |- ( A i^i B ) = S
  assume offval.6: |- ( ( ph /\ x e. A ) -> ( F ` x ) = C )
  assume offval.7: |- ( ( ph /\ x e. B ) -> ( G ` x ) = D )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint S x
  disjoint R x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint X x
  disjoint R f
  disjoint R g
  assert |- ( ph -> ( F oF R G ) = ( x e. S |-> ( C R D ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    #
    co
    #
    vx
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    vx
    cv
    #
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    vx
    cS
    @8
    cmpt
    #
    vx
    cS
    cC
    cD
    cR
    co
    #
    cmpt
    wph
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @1
    @9
    wceq
    wph
    cF
    cA
    wfn
    #
    cA
    cV
    wcel
    #
    @12
    offval.1
    offval.3
    cA
    cV
    cF
    fnex
    syl2anc
    wph
    cG
    cB
    wfn
    #
    cB
    cW
    wcel
    @13
    offval.2
    offval.4
    cB
    cW
    cG
    fnex
    syl2anc
    wph
    @9
    @10
    cvv
    wph
    vx
    @4
    cS
    @8
    wph
    @4
    cA
    cB
    cin
    #
    cS
    wph
    @2
    cA
    @3
    cB
    wph
    @14
    @2
    cA
    wceq
    offval.1
    cA
    cF
    fndm
    syl
    wph
    @16
    @3
    cB
    wceq
    offval.2
    cB
    cG
    fndm
    syl
    ineq12d
    offval.5
    syl6eq
    mpteq1d
    #
    wph
    @15
    cS
    cvv
    wcel
    @10
    cvv
    wcel
    offval.3
    @15
    cS
    @17
    cvv
    offval.5
    cA
    cB
    cV
    inex1g
    syl5eqelr
    vx
    cS
    @8
    cvv
    mptexg
    3syl
    eqeltrd
    vf
    vg
    cF
    cG
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    #
    vg
    cv
    #
    cdm
    #
    cin
    #
    @5
    @19
    cfv
    #
    @5
    @21
    cfv
    #
    cR
    co
    #
    cmpt
    @9
    @0
    cvv
    @19
    cF
    wceq
    #
    @21
    cG
    wceq
    #
    wa
    vx
    @23
    @26
    @4
    @8
    @27
    @28
    @20
    @2
    @22
    @3
    @19
    cF
    dmeq
    @21
    cG
    dmeq
    ineqan12d
    @27
    @28
    @24
    @6
    @25
    @7
    cR
    @5
    @19
    cF
    fveq1
    @5
    @21
    cG
    fveq1
    oveqan12d
    mpteq12dv
    vx
    cR
    vf
    vg
    df-of
    ovmpt2ga
    syl3anc
    @18
    wph
    vx
    cS
    @8
    @11
    @5
    cS
    wcel
    #
    wph
    @5
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    @8
    @11
    wceq
    @29
    @5
    @17
    wcel
    @32
    @17
    cS
    @5
    offval.5
    eleq2i
    @5
    cA
    cB
    elin
    bitr3i
    wph
    @32
    wa
    @6
    cC
    @7
    cD
    cR
    wph
    @30
    @6
    cC
    wceq
    @31
    offval.6
    adantrr
    wph
    @31
    @7
    cD
    wceq
    @30
    offval.7
    adantrl
    oveq12d
    sylan2b
    mpteq2dva
    3eqtrd
end
