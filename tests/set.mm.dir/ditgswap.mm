include "cdit.mm"
include "cneg.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1d.mm"
include "wa.mm"
include "cioo.mm"
include "citg.mm"
include "simpr.mm"
include "adantr.mm"
include "ditgneg.mm"
include "ditgpos.mm"
include "negeqd.mm"
include "eqtr4d.mm"
include "cc.mm"
include "cv.mm"
include "cxr.mm"
include "wss.mm"
include "rexrd.mm"
include "simp2d.mm"
include "iooss1.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
include "sselda.mm"
include "cmpt.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "syldan.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "a1i.mm"
include "iblss.mm"
include "itgcl.mm"
include "negnegd.mm"
include "3eqtr4rd.mm"
include "lecasei.mm"

theorem ditgswap
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ditgcl.x: |- ( ph -> X e. RR )
  assume ditgcl.y: |- ( ph -> Y e. RR )
  assume ditgcl.a: |- ( ph -> A e. ( X [,] Y ) )
  assume ditgcl.b: |- ( ph -> B e. ( X [,] Y ) )
  assume ditgcl.c: |- ( ( ph /\ x e. ( X (,) Y ) ) -> C e. V )
  assume ditgcl.i: |- ( ph -> ( x e. ( X (,) Y ) |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ph -> S_ [ B -> A ] C _d x = -u S_ [ A -> B ] C _d x )

  proof
    wph
    vx
    cB
    cA
    cC
    cdit
    #
    vx
    cA
    cB
    cC
    cdit
    #
    cneg
    #
    wceq
    cA
    cB
    wph
    cA
    cr
    wcel
    #
    cX
    cA
    cle
    wbr
    #
    cA
    cY
    cle
    wbr
    #
    wph
    cA
    cX
    cY
    cicc
    co
    #
    wcel
    #
    @3
    @4
    @5
    w3a
    #
    ditgcl.a
    wph
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @7
    @8
    wb
    ditgcl.x
    ditgcl.y
    cX
    cY
    cA
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    wph
    cB
    cr
    wcel
    #
    cX
    cB
    cle
    wbr
    #
    cB
    cY
    cle
    wbr
    #
    wph
    cB
    @6
    wcel
    #
    @13
    @14
    @15
    w3a
    #
    ditgcl.b
    wph
    @9
    @10
    @16
    @17
    wb
    ditgcl.x
    ditgcl.y
    cX
    cY
    cB
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    wph
    cA
    cB
    cle
    wbr
    #
    wa
    #
    @0
    vx
    cA
    cB
    cioo
    co
    cC
    citg
    #
    cneg
    @2
    @21
    vx
    cA
    cB
    cC
    wph
    @20
    simpr
    #
    wph
    @3
    @20
    @12
    adantr
    wph
    @13
    @20
    @19
    adantr
    ditgneg
    @21
    @1
    @22
    @21
    vx
    cA
    cB
    cC
    @23
    ditgpos
    negeqd
    eqtr4d
    wph
    cB
    cA
    cle
    wbr
    #
    wa
    #
    vx
    cB
    cA
    cioo
    co
    #
    cC
    citg
    #
    cneg
    #
    cneg
    @27
    @2
    @0
    @25
    @27
    wph
    @27
    cc
    wcel
    @24
    wph
    vx
    @26
    cC
    cc
    wph
    vx
    cv
    #
    @26
    wcel
    @29
    cX
    cY
    cioo
    co
    #
    wcel
    cC
    cc
    wcel
    wph
    @26
    @30
    @29
    wph
    @26
    cX
    cA
    cioo
    co
    #
    @30
    wph
    cX
    cxr
    wcel
    @14
    @26
    @31
    wss
    wph
    cX
    ditgcl.x
    rexrd
    wph
    @13
    @14
    @15
    @18
    simp2d
    cX
    cB
    cA
    iooss1
    syl2anc
    wph
    cY
    cxr
    wcel
    @5
    @31
    @30
    wss
    wph
    cY
    ditgcl.y
    rexrd
    wph
    @3
    @4
    @5
    @11
    simp3d
    cX
    cA
    cY
    iooss2
    syl2anc
    sstrd
    #
    sselda
    wph
    vx
    @30
    cC
    cV
    wph
    vx
    @30
    cC
    cmpt
    #
    cibl
    wcel
    @33
    cmbf
    wcel
    ditgcl.i
    @33
    iblmbf
    syl
    ditgcl.c
    mbfmptcl
    syldan
    wph
    vx
    @26
    @30
    cC
    cV
    @32
    @26
    cvol
    cdm
    wcel
    wph
    cB
    cA
    ioombl
    a1i
    ditgcl.c
    ditgcl.i
    iblss
    itgcl
    adantr
    negnegd
    @25
    @1
    @28
    @25
    vx
    cB
    cA
    cC
    wph
    @24
    simpr
    #
    wph
    @13
    @24
    @19
    adantr
    wph
    @3
    @24
    @12
    adantr
    ditgneg
    negeqd
    @25
    vx
    cB
    cA
    cC
    @34
    ditgpos
    3eqtr4rd
    lecasei
end
