include "cdit.mm"
include "cc.mm"
include "wcel.mm"
include "cr.mm"
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
include "ditgpos.mm"
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
include "syldan.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "a1i.mm"
include "iblss.mm"
include "itgcl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "cneg.mm"
include "ditgneg.mm"
include "negcld.mm"
include "lecasei.mm"

theorem ditgcl
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
  assert |- ( ph -> S_ [ A -> B ] C _d x e. CC )

  proof
    wph
    vx
    cA
    cB
    cC
    cdit
    #
    cc
    wcel
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
    @1
    @2
    @3
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
    @5
    @6
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
    @4
    wcel
    #
    @11
    @12
    @13
    w3a
    #
    ditgcl.b
    wph
    @7
    @8
    @14
    @15
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
    #
    cC
    citg
    #
    cc
    @19
    vx
    cA
    cB
    cC
    wph
    @18
    simpr
    ditgpos
    wph
    @21
    cc
    wcel
    @18
    wph
    vx
    @20
    cC
    cV
    wph
    vx
    cv
    #
    @20
    wcel
    @22
    cX
    cY
    cioo
    co
    #
    wcel
    #
    cC
    cV
    wcel
    #
    wph
    @20
    @23
    @22
    wph
    @20
    cX
    cB
    cioo
    co
    #
    @23
    wph
    cX
    cxr
    wcel
    #
    @2
    @20
    @26
    wss
    wph
    cX
    ditgcl.x
    rexrd
    #
    wph
    @1
    @2
    @3
    @9
    simp2d
    cX
    cA
    cB
    iooss1
    syl2anc
    wph
    cY
    cxr
    wcel
    #
    @13
    @26
    @23
    wss
    wph
    cY
    ditgcl.y
    rexrd
    #
    wph
    @11
    @12
    @13
    @16
    simp3d
    cX
    cB
    cY
    iooss2
    syl2anc
    sstrd
    #
    sselda
    ditgcl.c
    syldan
    wph
    vx
    @20
    @23
    cC
    cV
    @31
    @20
    cvol
    cdm
    #
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    ditgcl.c
    ditgcl.i
    iblss
    itgcl
    adantr
    eqeltrd
    wph
    cB
    cA
    cle
    wbr
    #
    wa
    #
    @0
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
    cc
    @34
    vx
    cB
    cA
    cC
    wph
    @33
    simpr
    wph
    @11
    @33
    @17
    adantr
    wph
    @1
    @33
    @10
    adantr
    ditgneg
    wph
    @37
    cc
    wcel
    @33
    wph
    @36
    wph
    vx
    @35
    cC
    cV
    wph
    @22
    @35
    wcel
    @24
    @25
    wph
    @35
    @23
    @22
    wph
    @35
    cX
    cA
    cioo
    co
    #
    @23
    wph
    @27
    @12
    @35
    @38
    wss
    @28
    wph
    @11
    @12
    @13
    @16
    simp2d
    cX
    cB
    cA
    iooss1
    syl2anc
    wph
    @29
    @3
    @38
    @23
    wss
    @30
    wph
    @1
    @2
    @3
    @9
    simp3d
    cX
    cA
    cY
    iooss2
    syl2anc
    sstrd
    #
    sselda
    ditgcl.c
    syldan
    wph
    vx
    @35
    @23
    cC
    cV
    @39
    @35
    @32
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
    negcld
    adantr
    eqeltrd
    lecasei
end
