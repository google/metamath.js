include "cdit.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cioo.mm"
include "citg.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1d.mm"
include "adantr.mm"
include "simpr.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "mpbir3and.mm"
include "cv.mm"
include "cc.mm"
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
include "adantlr.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "a1i.mm"
include "iblss.mm"
include "itgsplitioo.mm"
include "letrd.mm"
include "ditgpos.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "anassrs.mm"

theorem ditgsplitlem
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ditgsplit.x: |- ( ph -> X e. RR )
  assume ditgsplit.y: |- ( ph -> Y e. RR )
  assume ditgsplit.a: |- ( ph -> A e. ( X [,] Y ) )
  assume ditgsplit.b: |- ( ph -> B e. ( X [,] Y ) )
  assume ditgsplit.c: |- ( ph -> C e. ( X [,] Y ) )
  assume ditgsplit.d: |- ( ( ph /\ x e. ( X (,) Y ) ) -> D e. V )
  assume ditgsplit.i: |- ( ph -> ( x e. ( X (,) Y ) |-> D ) e. L^1 )
  assume ditgsplit.1: |- ( ( ps /\ th ) <-> ( A <_ B /\ B <_ C ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint ps x
  disjoint th x
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( ( ph /\ ps ) /\ th ) -> S_ [ A -> C ] D _d x = ( S_ [ A -> B ] D _d x + S_ [ B -> C ] D _d x ) )

  proof
    wph
    wps
    wth
    vx
    cA
    cC
    cD
    cdit
    #
    vx
    cA
    cB
    cD
    cdit
    #
    vx
    cB
    cC
    cD
    cdit
    #
    caddc
    co
    #
    wceq
    wph
    wps
    wth
    wa
    #
    wa
    #
    vx
    cA
    cC
    cioo
    co
    #
    cD
    citg
    vx
    cA
    cB
    cioo
    co
    #
    cD
    citg
    #
    vx
    cB
    cC
    cioo
    co
    #
    cD
    citg
    #
    caddc
    co
    @0
    @3
    @5
    vx
    cA
    cB
    cC
    cD
    wph
    cA
    cr
    wcel
    #
    @4
    wph
    @11
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
    @11
    @12
    @13
    w3a
    #
    ditgsplit.a
    wph
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @15
    @16
    wb
    ditgsplit.x
    ditgsplit.y
    cX
    cY
    cA
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    adantr
    #
    wph
    cC
    cr
    wcel
    #
    @4
    wph
    @22
    cX
    cC
    cle
    wbr
    #
    cC
    cY
    cle
    wbr
    #
    wph
    cC
    @14
    wcel
    #
    @22
    @23
    @24
    w3a
    #
    ditgsplit.c
    wph
    @17
    @18
    @25
    @26
    wb
    ditgsplit.x
    ditgsplit.y
    cX
    cY
    cC
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    adantr
    #
    @5
    cB
    cA
    cC
    cicc
    co
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    wph
    @31
    @4
    wph
    @31
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
    @14
    wcel
    #
    @31
    @34
    @35
    w3a
    #
    ditgsplit.b
    wph
    @17
    @18
    @36
    @37
    wb
    ditgsplit.x
    ditgsplit.y
    cX
    cY
    cB
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    adantr
    #
    @5
    @32
    @33
    @5
    @4
    @32
    @33
    wa
    wph
    @4
    simpr
    ditgsplit.1
    sylib
    #
    simpld
    #
    @5
    @32
    @33
    @40
    simprd
    #
    wph
    @30
    @31
    @32
    @33
    w3a
    wb
    #
    @4
    wph
    @11
    @22
    @43
    @20
    @28
    cA
    cC
    cB
    elicc2
    syl2anc
    adantr
    mpbir3and
    wph
    vx
    cv
    #
    @6
    wcel
    #
    cD
    cc
    wcel
    #
    @4
    wph
    @45
    @44
    cX
    cY
    cioo
    co
    #
    wcel
    @46
    wph
    @6
    @47
    @44
    wph
    @6
    cX
    cC
    cioo
    co
    #
    @47
    wph
    cX
    cxr
    wcel
    #
    @12
    @6
    @48
    wss
    wph
    cX
    ditgsplit.x
    rexrd
    #
    wph
    @11
    @12
    @13
    @19
    simp2d
    #
    cX
    cA
    cC
    iooss1
    syl2anc
    wph
    cY
    cxr
    wcel
    #
    @24
    @48
    @47
    wss
    wph
    cY
    ditgsplit.y
    rexrd
    #
    wph
    @22
    @23
    @24
    @27
    simp3d
    cX
    cC
    cY
    iooss2
    syl2anc
    #
    sstrd
    sselda
    wph
    vx
    @47
    cD
    cV
    wph
    vx
    @47
    cD
    cmpt
    #
    cibl
    wcel
    @55
    cmbf
    wcel
    ditgsplit.i
    @55
    iblmbf
    syl
    ditgsplit.d
    mbfmptcl
    syldan
    adantlr
    wph
    vx
    @7
    cD
    cmpt
    cibl
    wcel
    @4
    wph
    vx
    @7
    @47
    cD
    cV
    wph
    @7
    cX
    cB
    cioo
    co
    #
    @47
    wph
    @49
    @12
    @7
    @56
    wss
    @50
    @51
    cX
    cA
    cB
    iooss1
    syl2anc
    wph
    @52
    @35
    @56
    @47
    wss
    @53
    wph
    @31
    @34
    @35
    @38
    simp3d
    cX
    cB
    cY
    iooss2
    syl2anc
    sstrd
    @7
    cvol
    cdm
    #
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    ditgsplit.d
    ditgsplit.i
    iblss
    adantr
    wph
    vx
    @9
    cD
    cmpt
    cibl
    wcel
    @4
    wph
    vx
    @9
    @47
    cD
    cV
    wph
    @9
    @48
    @47
    wph
    @49
    @34
    @9
    @48
    wss
    @50
    wph
    @31
    @34
    @35
    @38
    simp2d
    cX
    cB
    cC
    iooss1
    syl2anc
    @54
    sstrd
    @9
    @57
    wcel
    wph
    cB
    cC
    ioombl
    a1i
    ditgsplit.d
    ditgsplit.i
    iblss
    adantr
    itgsplitioo
    @5
    vx
    cA
    cC
    cD
    @5
    cA
    cB
    cC
    @21
    @39
    @29
    @41
    @42
    letrd
    ditgpos
    @5
    @1
    @8
    @2
    @10
    caddc
    @5
    vx
    cA
    cB
    cD
    @41
    ditgpos
    @5
    vx
    cB
    cC
    cD
    @42
    ditgpos
    oveq12d
    3eqtr4d
    anassrs
end
