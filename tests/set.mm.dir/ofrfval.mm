include "cofr.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "cin.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "wfn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wa.mm"
include "dmeq.mm"
include "ineqan12d.mm"
include "fveq1.mm"
include "breqan12d.mm"
include "raleqbidv.mm"
include "df-ofr.mm"
include "brabga.mm"
include "fndm.mm"
include "syl.mm"
include "ineq12d.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "inss1.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "sylan2.mm"
include "inss2.mm"
include "breq12d.mm"
include "ralbidva.mm"
include "3bitrd.mm"

theorem ofrfval
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
  assert |- ( ph -> ( F oR R G <-> A. x e. S C R D ) )

  proof
    wph
    cF
    cG
    cR
    cofr
    #
    wbr
    #
    vx
    cv
    #
    cF
    cfv
    #
    @2
    cG
    cfv
    #
    cR
    wbr
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
    wral
    #
    @5
    vx
    cS
    wral
    cC
    cD
    cR
    wbr
    #
    vx
    cS
    wral
    wph
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    @1
    @9
    wb
    wph
    cF
    cA
    wfn
    #
    cA
    cV
    wcel
    @11
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
    @12
    offval.2
    offval.4
    cB
    cW
    cG
    fnex
    syl2anc
    @2
    vf
    cv
    #
    cfv
    #
    @2
    vg
    cv
    #
    cfv
    #
    cR
    wbr
    #
    vx
    @15
    cdm
    #
    @17
    cdm
    #
    cin
    #
    wral
    @9
    vf
    vg
    cF
    cG
    @0
    cvv
    cvv
    @15
    cF
    wceq
    #
    @17
    cG
    wceq
    #
    wa
    @19
    @5
    vx
    @22
    @8
    @23
    @24
    @20
    @6
    @21
    @7
    @15
    cF
    dmeq
    @17
    cG
    dmeq
    ineqan12d
    @23
    @24
    @16
    @3
    @18
    @4
    cR
    @2
    @15
    cF
    fveq1
    @2
    @17
    cG
    fveq1
    breqan12d
    raleqbidv
    vx
    cR
    vf
    vg
    df-ofr
    brabga
    syl2anc
    wph
    @5
    vx
    @8
    cS
    wph
    @8
    cA
    cB
    cin
    #
    cS
    wph
    @6
    cA
    @7
    cB
    wph
    @13
    @6
    cA
    wceq
    offval.1
    cA
    cF
    fndm
    syl
    wph
    @14
    @7
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
    raleqdv
    wph
    @5
    @10
    vx
    cS
    wph
    @2
    cS
    wcel
    #
    wa
    @3
    cC
    @4
    cD
    cR
    @26
    wph
    @2
    cA
    wcel
    @3
    cC
    wceq
    cS
    cA
    @2
    cS
    @25
    cA
    offval.5
    cA
    cB
    inss1
    eqsstr3i
    sseli
    offval.6
    sylan2
    @26
    wph
    @2
    cB
    wcel
    @4
    cD
    wceq
    cS
    cB
    @2
    cS
    @25
    cB
    offval.5
    cA
    cB
    inss2
    eqsstr3i
    sseli
    offval.7
    sylan2
    breq12d
    ralbidva
    3bitrd
end
