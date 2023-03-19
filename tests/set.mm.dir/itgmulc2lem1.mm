include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "citg.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cpnf.mm"
include "cico.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0icopnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cmbf.mm"
include "cibl.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "itg2mulc.mm"
include "cvv.mm"
include "reex.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "offval2.mm"
include "ovif2.mm"
include "mul01d.mm"
include "ifeq2d.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "itgposval.mm"
include "oveq2d.mm"
include "remulcld.mm"
include "iblmulc2.mm"
include "mulge0d.mm"
include "3eqtr4d.mm"

theorem itgmulc2lem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume itgmulc2.1: |- ( ph -> C e. CC )
  assume itgmulc2.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgmulc2.3: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgmulc2.4: |- ( ph -> C e. RR )
  assume itgmulc2.5: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgmulc2.6: |- ( ph -> 0 <_ C )
  assume itgmulc2.7: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> ( C x. S. A B _d x ) = S. A ( C x. B ) _d x )

  proof
    wph
    cC
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vx
    cr
    @1
    cC
    cB
    cmul
    co
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cC
    vx
    cA
    cB
    citg
    #
    cmul
    co
    vx
    cA
    @6
    citg
    wph
    cr
    cC
    csn
    cxp
    #
    @3
    cmul
    cof
    co
    #
    citg2
    cfv
    @5
    @9
    wph
    cC
    @3
    wph
    vx
    cr
    @2
    cc0
    cpnf
    cico
    co
    #
    @3
    wph
    @2
    @13
    wcel
    @0
    cr
    wcel
    #
    wph
    @1
    cB
    cc0
    @13
    wph
    @1
    wa
    #
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cB
    @13
    wcel
    itgmulc2.5
    itgmulc2.7
    cB
    elrege0
    sylanbrc
    cc0
    @13
    wcel
    wph
    @1
    wn
    wa
    0e0icopnf
    a1i
    ifclda
    adantr
    #
    @3
    eqid
    fmptd
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @4
    cr
    wcel
    #
    wph
    @17
    cibl
    wcel
    @18
    @19
    wa
    itgmulc2.3
    wph
    vx
    cA
    cB
    itgmulc2.5
    itgmulc2.7
    iblpos
    mpbid
    simprd
    wph
    cC
    cr
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    cC
    @13
    wcel
    itgmulc2.4
    itgmulc2.6
    cC
    elrege0
    sylanbrc
    itg2mulc
    wph
    @12
    @8
    citg2
    wph
    @12
    vx
    cr
    cC
    @2
    cmul
    co
    #
    cmpt
    @8
    wph
    vx
    cr
    cC
    @2
    cmul
    @11
    @3
    cvv
    cr
    @13
    cr
    cvv
    wcel
    wph
    reex
    a1i
    wph
    @20
    @14
    itgmulc2.4
    adantr
    @16
    @11
    vx
    cr
    cC
    cmpt
    wceq
    wph
    vx
    cr
    cC
    fconstmpt
    a1i
    wph
    @3
    eqidd
    offval2
    wph
    vx
    cr
    @22
    @7
    wph
    @14
    wa
    #
    @22
    @1
    @6
    cC
    cc0
    cmul
    co
    #
    cif
    @7
    @1
    cC
    cB
    cc0
    cmul
    ovif2
    @23
    @1
    @24
    cc0
    @6
    wph
    @24
    cc0
    wceq
    @14
    wph
    cC
    itgmulc2.1
    mul01d
    adantr
    ifeq2d
    syl5eq
    mpteq2dva
    eqtrd
    fveq2d
    eqtr3d
    wph
    @10
    @4
    cC
    cmul
    wph
    vx
    cA
    cB
    itgmulc2.5
    itgmulc2.3
    itgmulc2.7
    itgposval
    oveq2d
    wph
    vx
    cA
    @6
    @15
    cC
    cB
    wph
    @20
    @1
    itgmulc2.4
    adantr
    #
    itgmulc2.5
    remulcld
    wph
    vx
    cA
    cB
    cC
    cV
    itgmulc2.1
    itgmulc2.2
    itgmulc2.3
    iblmulc2
    @15
    cC
    cB
    @25
    itgmulc2.5
    wph
    @21
    @1
    itgmulc2.6
    adantr
    itgmulc2.7
    mulge0d
    itgposval
    3eqtr4d
end
