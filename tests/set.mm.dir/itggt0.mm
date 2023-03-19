include "cc0.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "citg.mm"
include "clt.mm"
include "crp.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfdm2.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "rpred.mm"
include "rpge0d.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0icopnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "mblss.mm"
include "rembl.mm"
include "cdif.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "syl5eqel.mm"
include "mbfss.mm"
include "wral.mm"
include "rpgt0d.mm"
include "wceq.mm"
include "sselda.mm"
include "eqeltrd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "itg2gt0.mm"
include "itgposval.mm"

theorem itggt0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume itggt0.1: |- ( ph -> 0 < ( vol ` A ) )
  assume itggt0.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itggt0.3: |- ( ( ph /\ x e. A ) -> B e. RR+ )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> 0 < S. A B _d x )

  proof
    wph
    cc0
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
    vx
    cA
    cB
    citg
    clt
    wph
    vy
    cA
    @3
    wph
    vx
    cA
    cB
    crp
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @4
    cmbf
    wcel
    itggt0.2
    @4
    iblmbf
    syl
    #
    itggt0.3
    mbfdm2
    #
    itggt0.1
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
    @7
    wcel
    #
    @0
    cr
    wcel
    #
    wph
    @1
    cB
    cc0
    @7
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
    @7
    wcel
    @10
    cB
    itggt0.3
    rpred
    #
    @10
    cB
    itggt0.3
    rpge0d
    #
    cB
    elrege0
    sylanbrc
    cc0
    @7
    wcel
    wph
    @1
    wn
    #
    wa
    0e0icopnf
    a1i
    ifclda
    #
    adantr
    @3
    eqid
    #
    fmptd
    wph
    vx
    cA
    cr
    @2
    @7
    wph
    cA
    cvol
    cdm
    #
    wcel
    cA
    cr
    wss
    @6
    cA
    mblss
    syl
    #
    cr
    @16
    wcel
    wph
    rembl
    a1i
    wph
    @8
    @1
    @14
    adantr
    wph
    @0
    cr
    cA
    cdif
    wcel
    #
    wa
    @1
    cB
    cc0
    @18
    @13
    wph
    @0
    cr
    cA
    eldifn
    adantl
    iffalsed
    wph
    vx
    cA
    @2
    cmpt
    @4
    cmbf
    vx
    cA
    @2
    cB
    @1
    cB
    cc0
    iftrue
    #
    mpteq2ia
    @5
    syl5eqel
    mbfss
    wph
    cc0
    vy
    cv
    #
    @3
    cfv
    #
    clt
    wbr
    #
    vy
    cA
    wph
    cc0
    @0
    @3
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    wral
    @22
    vy
    cA
    wral
    wph
    @24
    vx
    cA
    @10
    cc0
    cB
    @23
    clt
    @10
    cB
    itggt0.3
    rpgt0d
    @10
    @23
    @2
    cB
    @10
    @9
    @2
    crp
    wcel
    @23
    @2
    wceq
    wph
    cA
    cr
    @0
    @17
    sselda
    @10
    @2
    cB
    crp
    @1
    @2
    cB
    wceq
    wph
    @19
    adantl
    #
    itggt0.3
    eqeltrd
    vx
    cr
    @2
    crp
    @3
    @15
    fvmpt2
    syl2anc
    @25
    eqtrd
    breqtrrd
    ralrimiva
    @22
    @24
    vy
    vx
    cA
    vx
    cc0
    @21
    clt
    vx
    cc0
    nfcv
    vx
    clt
    nfcv
    vx
    cr
    @2
    @20
    nffvmpt1
    nfbr
    @24
    vy
    nfv
    @20
    @0
    wceq
    @21
    @23
    cc0
    clt
    @20
    @0
    @3
    fveq2
    breq2d
    cbvral
    sylibr
    r19.21bi
    itg2gt0
    wph
    vx
    cA
    cB
    @11
    itggt0.2
    @12
    itgposval
    breqtrrd
end
