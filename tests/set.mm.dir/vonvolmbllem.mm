include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "covoln.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "covol.mm"
include "cr.mm"
include "nfcv.mm"
include "ssmapsn.mm"
include "ineq1d.mm"
include "cvv.mm"
include "wcel.mm"
include "reex.mm"
include "a1i.mm"
include "cv.mm"
include "crn.mm"
include "ciun.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "sselda.mm"
include "elmapi.mm"
include "syl.mm"
include "frn.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "ssexd.mm"
include "snex.mm"
include "inmap.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "ssinss1d.mm"
include "ovnovol.mm"
include "difeq1d.mm"
include "difmapsn.mm"
include "ssdifssd.mm"
include "oveq12d.mm"
include "cpw.mm"
include "wceq.mm"
include "elpwd.mm"
include "fveq2.mm"
include "ineq1.mm"
include "difeq1.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"

theorem vonvolmbllem
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume vonvolmbllem.a: |- ( ph -> A e. V )
  assume vonvolmbllem.b: |- ( ph -> B C_ RR )
  assume vonvolmbllem.e: |- ( ph -> A. y e. ~P RR ( vol* ` y ) = ( ( vol* ` ( y i^i B ) ) +e ( vol* ` ( y \ B ) ) ) )
  assume vonvolmbllem.x: |- ( ph -> X C_ ( RR ^m { A } ) )
  assume vonvolmbllem.y: |- Y = U_ f e. X ran f

  disjoint A f
  disjoint B y
  disjoint X f
  disjoint Y f
  disjoint Y y
  disjoint f ph
  disjoint k x
  assert |- ( ph -> ( ( ( voln* ` { A } ) ` ( X i^i ( B ^m { A } ) ) ) +e ( ( voln* ` { A } ) ` ( X \ ( B ^m { A } ) ) ) ) = ( ( voln* ` { A } ) ` X ) )

  proof
    wph
    cX
    cB
    cA
    csn
    #
    cmap
    co
    #
    cin
    #
    @0
    covoln
    cfv
    #
    cfv
    #
    cX
    @1
    cdif
    #
    @3
    cfv
    #
    cxad
    co
    cY
    cB
    cin
    #
    covol
    cfv
    #
    cY
    cB
    cdif
    #
    covol
    cfv
    #
    cxad
    co
    #
    cX
    @3
    cfv
    #
    wph
    @4
    @8
    @6
    @10
    cxad
    wph
    @4
    @7
    @0
    cmap
    co
    #
    @3
    cfv
    @8
    wph
    @2
    @13
    @3
    wph
    @2
    cY
    @0
    cmap
    co
    #
    @1
    cin
    @13
    wph
    cX
    @14
    @1
    wph
    cA
    cr
    cX
    cY
    vf
    cV
    vf
    cY
    nfcv
    vonvolmbllem.a
    vonvolmbllem.x
    vonvolmbllem.y
    ssmapsn
    #
    ineq1d
    wph
    cY
    cB
    @0
    cvv
    cvv
    cvv
    wph
    cY
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    wph
    cY
    vf
    cX
    vf
    cv
    #
    crn
    #
    ciun
    #
    cr
    vonvolmbllem.y
    wph
    @18
    cr
    wss
    #
    vf
    cX
    wral
    @19
    cr
    wss
    wph
    @20
    vf
    cX
    wph
    @17
    cX
    wcel
    wa
    #
    @0
    cr
    @17
    wf
    #
    @20
    @21
    @17
    cr
    @0
    cmap
    co
    #
    wcel
    @22
    wph
    cX
    @23
    @17
    vonvolmbllem.x
    sselda
    @17
    cr
    @0
    elmapi
    syl
    @0
    cr
    @17
    frn
    syl
    ralrimiva
    vf
    cX
    @18
    cr
    iunss
    sylibr
    syl5eqss
    #
    ssexd
    #
    wph
    cB
    cr
    cvv
    @16
    vonvolmbllem.b
    ssexd
    #
    @0
    cvv
    wcel
    wph
    cA
    snex
    a1i
    inmap
    eqtrd
    fveq2d
    wph
    cA
    @7
    cV
    vonvolmbllem.a
    wph
    cY
    cB
    cr
    @24
    ssinss1d
    ovnovol
    eqtrd
    wph
    @6
    @9
    @0
    cmap
    co
    #
    @3
    cfv
    @10
    wph
    @5
    @27
    @3
    wph
    @5
    @14
    @1
    cdif
    @27
    wph
    cX
    @14
    @1
    @15
    difeq1d
    wph
    cY
    cB
    cA
    cvv
    cvv
    cV
    @25
    @26
    vonvolmbllem.a
    difmapsn
    eqtrd
    fveq2d
    wph
    cA
    @9
    cV
    vonvolmbllem.a
    wph
    cY
    cr
    cB
    @24
    ssdifssd
    ovnovol
    eqtrd
    oveq12d
    wph
    @12
    @14
    @3
    cfv
    cY
    covol
    cfv
    #
    @11
    wph
    cX
    @14
    @3
    @15
    fveq2d
    wph
    cA
    cY
    cV
    vonvolmbllem.a
    @24
    ovnovol
    wph
    cY
    cr
    cpw
    #
    wcel
    vy
    cv
    #
    covol
    cfv
    #
    @30
    cB
    cin
    #
    covol
    cfv
    #
    @30
    cB
    cdif
    #
    covol
    cfv
    #
    cxad
    co
    #
    wceq
    #
    vy
    @29
    wral
    @28
    @11
    wceq
    #
    wph
    cY
    cr
    cvv
    @25
    @24
    elpwd
    vonvolmbllem.e
    @37
    @38
    vy
    cY
    @29
    @30
    cY
    wceq
    #
    @31
    @28
    @36
    @11
    @30
    cY
    covol
    fveq2
    @39
    @33
    @8
    @35
    @10
    cxad
    @39
    @32
    @7
    covol
    @30
    cY
    cB
    ineq1
    fveq2d
    @39
    @34
    @9
    covol
    @30
    cY
    cB
    difeq1
    fveq2d
    oveq12d
    eqeq12d
    rspcva
    syl2anc
    3eqtrd
    eqtr4d
end
