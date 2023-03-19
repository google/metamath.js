include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cdit.mm"
include "cioo.mm"
include "citg.mm"
include "cmin.mm"
include "simpr.mm"
include "ditgpos.mm"
include "cicc.mm"
include "cres.mm"
include "wcel.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "adantr.mm"
include "cc.mm"
include "ccncf.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "wf.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cncff.mm"
include "syl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "iccntr.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "cxr.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp2d.mm"
include "iooss1.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "cmpt.mm"
include "cibl.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmptd.mm"
include "cvv.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "fvexd.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "iccss2.mm"
include "ftc2.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "itgeq2dv.mm"
include "ubicc2.mm"
include "lbicc2.mm"
include "oveqan12d.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"

theorem ftc2ditglem
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  assume ftc2ditg.x: |- ( ph -> X e. RR )
  assume ftc2ditg.y: |- ( ph -> Y e. RR )
  assume ftc2ditg.a: |- ( ph -> A e. ( X [,] Y ) )
  assume ftc2ditg.b: |- ( ph -> B e. ( X [,] Y ) )
  assume ftc2ditg.c: |- ( ph -> ( RR _D F ) e. ( ( X (,) Y ) -cn-> CC ) )
  assume ftc2ditg.i: |- ( ph -> ( RR _D F ) e. L^1 )
  assume ftc2ditg.f: |- ( ph -> F e. ( ( X [,] Y ) -cn-> CC ) )

  disjoint A t
  disjoint B t
  disjoint F t
  disjoint ph t
  disjoint X t
  disjoint Y t
  assert |- ( ( ph /\ A <_ B ) -> S_ [ A -> B ] ( ( RR _D F ) ` t ) _d t = ( ( F ` B ) - ( F ` A ) ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    wa
    #
    vt
    cA
    cB
    vt
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cdit
    vt
    cA
    cB
    cioo
    co
    #
    @4
    citg
    #
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cmin
    co
    #
    @1
    vt
    cA
    cB
    @4
    wph
    @0
    simpr
    #
    ditgpos
    @1
    vt
    @5
    @2
    cr
    cF
    cA
    cB
    cicc
    co
    #
    cres
    #
    cdv
    co
    #
    cfv
    #
    citg
    cB
    @12
    cfv
    #
    cA
    @12
    cfv
    #
    cmin
    co
    #
    @6
    @9
    @1
    vt
    cA
    cB
    @12
    wph
    cA
    cr
    wcel
    #
    @0
    wph
    cX
    cY
    cicc
    co
    #
    cr
    cA
    wph
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @19
    cr
    wss
    #
    ftc2ditg.x
    ftc2ditg.y
    cX
    cY
    iccssre
    syl2anc
    #
    ftc2ditg.a
    sseldd
    #
    adantr
    #
    wph
    cB
    cr
    wcel
    #
    @0
    wph
    @19
    cr
    cB
    @23
    ftc2ditg.b
    sseldd
    #
    adantr
    #
    @10
    @1
    @13
    @3
    @5
    cres
    #
    @5
    cc
    ccncf
    co
    #
    @1
    @13
    @3
    @11
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @29
    @1
    cr
    cc
    wss
    #
    @19
    cc
    cF
    wf
    #
    @22
    @11
    cr
    wss
    #
    @13
    @33
    wceq
    @34
    @1
    ax-resscn
    a1i
    wph
    @35
    @0
    wph
    cF
    @19
    cc
    ccncf
    co
    wcel
    #
    @35
    ftc2ditg.f
    @19
    cc
    cF
    cncff
    syl
    adantr
    wph
    @22
    @0
    @23
    adantr
    wph
    @36
    @0
    wph
    @18
    @26
    @36
    @24
    @27
    cA
    cB
    iccssre
    syl2anc
    adantr
    @19
    @11
    cr
    @31
    cF
    ccnfld
    ctopn
    cfv
    #
    @38
    eqid
    #
    @38
    @39
    tgioo2
    dvres
    syl22anc
    @1
    @32
    @5
    @3
    wph
    @32
    @5
    wceq
    #
    @0
    wph
    @18
    @26
    @40
    @24
    @27
    cA
    cB
    iccntr
    syl2anc
    adantr
    reseq2d
    eqtrd
    #
    @1
    @5
    cX
    cY
    cioo
    co
    #
    wss
    #
    @3
    @42
    cc
    ccncf
    co
    wcel
    #
    @29
    @30
    wcel
    wph
    @43
    @0
    wph
    @5
    cX
    cB
    cioo
    co
    #
    @42
    wph
    cX
    cxr
    wcel
    cX
    cA
    cle
    wbr
    #
    @5
    @45
    wss
    wph
    cX
    ftc2ditg.x
    rexrd
    wph
    @18
    @46
    cA
    cY
    cle
    wbr
    #
    wph
    cA
    @19
    wcel
    #
    @18
    @46
    @47
    w3a
    #
    ftc2ditg.a
    wph
    @20
    @21
    @48
    @49
    wb
    ftc2ditg.x
    ftc2ditg.y
    cX
    cY
    cA
    elicc2
    syl2anc
    mpbid
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
    cB
    cY
    cle
    wbr
    #
    @45
    @42
    wss
    wph
    cY
    ftc2ditg.y
    rexrd
    wph
    @26
    cX
    cB
    cle
    wbr
    #
    @50
    wph
    cB
    @19
    wcel
    #
    @26
    @51
    @50
    w3a
    #
    ftc2ditg.b
    wph
    @20
    @21
    @52
    @53
    wb
    ftc2ditg.x
    ftc2ditg.y
    cX
    cY
    cB
    elicc2
    syl2anc
    mpbid
    simp3d
    cX
    cB
    cY
    iooss2
    syl2anc
    sstrd
    adantr
    #
    wph
    @44
    @0
    ftc2ditg.c
    adantr
    @42
    cc
    @5
    @3
    rescncf
    sylc
    eqeltrd
    @1
    @13
    vt
    @5
    @4
    cmpt
    #
    cibl
    @1
    @13
    @29
    @55
    @41
    @1
    @29
    vt
    @42
    @4
    cmpt
    #
    @5
    cres
    @55
    @1
    @3
    @56
    @5
    wph
    @3
    @56
    wceq
    @0
    wph
    vt
    @42
    cc
    @3
    wph
    @44
    @42
    cc
    @3
    wf
    ftc2ditg.c
    @42
    cc
    @3
    cncff
    syl
    feqmptd
    adantr
    #
    reseq1d
    @1
    vt
    @42
    @5
    @4
    @54
    resmptd
    eqtrd
    eqtrd
    @1
    vt
    @5
    @42
    @4
    cvv
    @54
    @5
    cvol
    cdm
    wcel
    @1
    cA
    cB
    ioombl
    a1i
    @1
    @2
    @42
    wcel
    wa
    @2
    @3
    fvexd
    @1
    @3
    @56
    cibl
    @57
    wph
    @3
    cibl
    wcel
    @0
    ftc2ditg.i
    adantr
    eqeltrrd
    iblss
    eqeltrd
    wph
    @12
    @11
    cc
    ccncf
    co
    wcel
    #
    @0
    wph
    @11
    @19
    wss
    #
    @37
    @58
    wph
    @48
    @52
    @59
    ftc2ditg.a
    ftc2ditg.b
    cX
    cY
    cA
    cB
    iccss2
    syl2anc
    ftc2ditg.f
    @19
    cc
    @11
    cF
    rescncf
    sylc
    adantr
    ftc2
    @1
    vt
    @5
    @14
    @4
    @1
    @2
    @5
    wcel
    @14
    @2
    @29
    cfv
    @4
    @1
    @2
    @13
    @29
    @41
    fveq1d
    @2
    @5
    @3
    fvres
    sylan9eq
    itgeq2dv
    @1
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @0
    @17
    @9
    wceq
    #
    @1
    cA
    @25
    rexrd
    @1
    cB
    @28
    rexrd
    @10
    @60
    @61
    @0
    w3a
    cB
    @11
    wcel
    #
    cA
    @11
    wcel
    #
    @62
    cA
    cB
    ubicc2
    cA
    cB
    lbicc2
    @63
    @64
    @15
    @7
    @16
    @8
    cmin
    cB
    @11
    cF
    fvres
    cA
    @11
    cF
    fvres
    oveqan12d
    syl2anc
    syl3anc
    3eqtr3d
    eqtrd
end
