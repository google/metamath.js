include "csitg.mm"
include "co.mm"
include "cfv.mm"
include "crn.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "cgsu.mm"
include "sitgfval.mm"
include "cvv.mm"
include "cdm.mm"
include "wcel.mm"
include "rnexg.mm"
include "difexg.mm"
include "3syl.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "simpl.mm"
include "sibfima.mm"
include "wfun.mm"
include "wss.mm"
include "wi.mm"
include "cr.mm"
include "csca.mm"
include "cbs.mm"
include "wf.mm"
include "crrh.mm"
include "cioo.mm"
include "ctg.mm"
include "ctopn.mm"
include "czlm.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "fveq2i.mm"
include "xpeq12i.mm"
include "reseq12i.mm"
include "eqtri.mm"
include "eqid.mm"
include "cdr.mm"
include "crrext.mm"
include "syl5eqel.mm"
include "rrextdrg.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "cnrg.mm"
include "rrextnrg.mm"
include "cnlm.mm"
include "rrextnlm.mm"
include "cchr.mm"
include "wceq.mm"
include "rrextchr.mm"
include "syl5eqr.mm"
include "ccusp.mm"
include "rrextcusp.mm"
include "cuss.mm"
include "cmetu.mm"
include "rrextust.mm"
include "rrhf.mm"
include "feq1i.mm"
include "sylibr.mm"
include "ffun.mm"
include "rge0ssre.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "funfvima2.mm"
include "syl2anc.mm"
include "sylc.mm"
include "cuni.mm"
include "cmeas.mm"
include "csiga.mm"
include "dmmeas.mm"
include "csigagen.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "sgsiga.mm"
include "sibfmbl.mm"
include "mbfmf.mm"
include "frn.mm"
include "unieqi.mm"
include "unisg.mm"
include "mp1i.mm"
include "syl5eq.mm"
include "ctps.mm"
include "tpsuni.mm"
include "eqtr4d.mm"
include "sseqtrd.mm"
include "ssdifd.mm"
include "sselda.mm"
include "eldifad.mm"
include "w3a.mm"
include "simp2.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "csupp.mm"
include "cfn.mm"
include "mptexg.mm"
include "c0g.mm"
include "suppimacnv.mm"
include "sylancl.mm"
include "sibfrn.mm"
include "cnvimass.mm"
include "dmmptss.mm"
include "sstri.mm"
include "difss.mm"
include "ssfi.mm"
include "eqeltrd.mm"
include "gsumcl2.mm"

theorem sitgclg
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cS: class S
  let c.x: class .x.
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sibfmbl.1: |- ( ph -> F e. dom ( W sitg M ) )
  assume sitgclg.g: |- G = ( Scalar ` W )
  assume sitgclg.d: |- D = ( ( dist ` G ) |` ( ( Base ` G ) X. ( Base ` G ) ) )
  assume sitgclg.1: |- ( ph -> W e. TopSp )
  assume sitgclg.2: |- ( ph -> W e. CMnd )
  assume sitgclg.3: |- ( ph -> ( Scalar ` W ) e. RRExt )
  assume sitgclg.4: |- ( ( ph /\ m e. ( H " ( 0 [,) +oo ) ) /\ x e. B ) -> ( m .x. x ) e. B )

  disjoint m x
  disjoint .0. m
  disjoint .0. x
  disjoint .x. m
  disjoint B m
  disjoint B x
  disjoint F m
  disjoint F x
  disjoint G m
  disjoint H m
  disjoint M m
  disjoint M x
  disjoint S m
  disjoint W m
  disjoint W x
  disjoint m ph
  disjoint ph x
  disjoint F x
  disjoint ph x
  disjoint B m
  disjoint F x
  disjoint H m
  disjoint m x
  disjoint M m
  disjoint M x
  disjoint S m
  disjoint W m
  disjoint W x
  disjoint .0. m
  disjoint .0. x
  disjoint .x. m
  disjoint A x
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint H f
  disjoint M f
  disjoint M g
  disjoint S f
  disjoint S g
  disjoint W f
  disjoint .x. f
  disjoint .0. f
  disjoint .0. g
  disjoint f ph
  disjoint f m
  disjoint f w
  disjoint B f
  disjoint m w
  disjoint B w
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint H f
  disjoint H w
  disjoint M f
  disjoint g m
  disjoint g w
  disjoint M g
  disjoint w x
  disjoint M w
  disjoint S f
  disjoint S g
  disjoint S w
  disjoint W f
  disjoint W g
  disjoint W w
  disjoint .0. f
  disjoint .0. g
  disjoint .0. w
  disjoint .x. f
  disjoint .x. w
  assert |- ( ph -> ( ( W sitg M ) ` F ) e. B )

  proof
    wph
    cF
    cW
    cM
    csitg
    co
    #
    cfv
    cW
    vx
    cF
    crn
    #
    c.0
    csn
    #
    cdif
    #
    cF
    ccnv
    vx
    cv
    #
    csn
    cima
    cM
    cfv
    #
    cH
    cfv
    #
    @4
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cB
    wph
    vx
    cB
    cS
    c.x
    cF
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sibfmbl.1
    sitgfval
    wph
    @3
    cB
    @8
    cW
    cvv
    c.0
    sitgval.b
    sitgval.0
    sitgclg.2
    wph
    cF
    @0
    cdm
    #
    wcel
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    #
    sibfmbl.1
    cF
    @9
    rnexg
    @1
    @2
    cvv
    difexg
    3syl
    #
    wph
    vx
    @3
    @7
    cB
    @8
    wph
    @4
    @3
    wcel
    #
    wa
    #
    wph
    @6
    cH
    cc0
    cpnf
    cico
    co
    #
    cima
    #
    wcel
    #
    @4
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    wph
    @12
    simpl
    #
    @13
    wph
    @5
    @14
    wcel
    #
    @16
    @19
    wph
    @4
    cB
    cS
    c.x
    cF
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sibfmbl.1
    sibfima
    wph
    cH
    wfun
    #
    @14
    cH
    cdm
    #
    wss
    @20
    @16
    wi
    wph
    cr
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cH
    wf
    #
    @21
    wph
    cr
    @24
    @23
    crrh
    cfv
    #
    wf
    @25
    wph
    @24
    cD
    @23
    cioo
    crn
    ctg
    cfv
    #
    cG
    ctopn
    cfv
    cG
    czlm
    cfv
    #
    cD
    cG
    cds
    cfv
    #
    cG
    cbs
    cfv
    #
    @30
    cxp
    #
    cres
    @23
    cds
    cfv
    #
    @24
    @24
    cxp
    #
    cres
    sitgclg.d
    @29
    @32
    @31
    @33
    cG
    @23
    cds
    sitgclg.g
    fveq2i
    @30
    @24
    @30
    @24
    cG
    @23
    cbs
    sitgclg.g
    fveq2i
    #
    @34
    xpeq12i
    reseq12i
    eqtri
    @27
    eqid
    @24
    eqid
    cG
    @23
    ctopn
    sitgclg.g
    fveq2i
    cG
    @23
    czlm
    sitgclg.g
    fveq2i
    wph
    @23
    cG
    cdr
    sitgclg.g
    wph
    cG
    crrext
    wcel
    #
    cG
    cdr
    wcel
    wph
    cG
    @23
    crrext
    sitgclg.g
    sitgclg.3
    syl5eqel
    #
    cG
    rrextdrg
    syl
    syl5eqelr
    wph
    @23
    cG
    cnrg
    sitgclg.g
    wph
    @35
    cG
    cnrg
    wcel
    @36
    cG
    rrextnrg
    syl
    syl5eqelr
    wph
    @35
    @28
    cnlm
    wcel
    @36
    cG
    @28
    @28
    eqid
    rrextnlm
    syl
    wph
    @23
    cchr
    cfv
    cG
    cchr
    cfv
    #
    cc0
    cG
    @23
    cchr
    sitgclg.g
    fveq2i
    wph
    @35
    @37
    cc0
    wceq
    @36
    cG
    rrextchr
    syl
    syl5eqr
    wph
    @23
    cG
    ccusp
    sitgclg.g
    wph
    @35
    cG
    ccusp
    wcel
    @36
    cG
    rrextcusp
    syl
    syl5eqelr
    wph
    @23
    cuss
    cfv
    cG
    cuss
    cfv
    #
    cD
    cmetu
    cfv
    #
    cG
    @23
    cuss
    sitgclg.g
    fveq2i
    wph
    @35
    @38
    @39
    wceq
    @36
    @30
    cD
    cG
    @30
    eqid
    sitgclg.d
    rrextust
    syl
    syl5eqr
    rrhf
    cr
    @24
    cH
    @26
    sitgval.h
    feq1i
    sylibr
    #
    cr
    @24
    cH
    ffun
    syl
    wph
    cr
    @14
    @22
    rge0ssre
    wph
    @25
    @22
    cr
    wceq
    @40
    cr
    @24
    cH
    fdm
    syl
    syl5sseqr
    @14
    @5
    cH
    funfvima2
    syl2anc
    sylc
    @13
    @4
    cB
    @2
    wph
    @3
    cB
    @2
    cdif
    @4
    wph
    @1
    cB
    @2
    wph
    @1
    cS
    cuni
    #
    cB
    wph
    cM
    cdm
    #
    cuni
    #
    @41
    cF
    wf
    @1
    @41
    wss
    wph
    @42
    cS
    cF
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    @42
    csiga
    crn
    cuni
    #
    wcel
    sitgval.2
    cM
    dmmeas
    syl
    wph
    cS
    cJ
    csigagen
    cfv
    #
    @44
    sitgval.s
    wph
    cJ
    cvv
    cJ
    cvv
    wcel
    #
    wph
    cJ
    cW
    ctopn
    cfv
    cvv
    sitgval.j
    cW
    ctopn
    fvex
    eqeltri
    #
    a1i
    sgsiga
    syl5eqel
    wph
    cB
    cS
    c.x
    cF
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sibfmbl.1
    sibfmbl
    mbfmf
    @43
    @41
    cF
    frn
    syl
    wph
    @41
    cJ
    cuni
    #
    cB
    wph
    @41
    @45
    cuni
    #
    @48
    cS
    @45
    sitgval.s
    unieqi
    @46
    @49
    @48
    wceq
    wph
    @47
    cJ
    cvv
    unisg
    mp1i
    syl5eq
    wph
    cW
    ctps
    wcel
    cB
    @48
    wceq
    sitgclg.1
    cB
    cJ
    cW
    sitgval.b
    sitgval.j
    tpsuni
    syl
    eqtr4d
    sseqtrd
    ssdifd
    sselda
    eldifad
    @16
    wph
    @16
    @17
    w3a
    #
    @18
    wph
    @16
    @17
    simp2
    wph
    vm
    cv
    #
    @15
    wcel
    #
    @17
    w3a
    #
    @51
    @4
    c.x
    co
    #
    cB
    wcel
    #
    wi
    @50
    @18
    wi
    vm
    @6
    @15
    @51
    @6
    wceq
    #
    @53
    @50
    @55
    @18
    @56
    @52
    @16
    wph
    @17
    @51
    @6
    @15
    eleq1
    3anbi2d
    @56
    @54
    @7
    cB
    @51
    @6
    @4
    c.x
    oveq1
    eleq1d
    imbi12d
    sitgclg.4
    vtoclg
    mpcom
    syl3anc
    @8
    eqid
    #
    fmptd
    wph
    @8
    c.0
    csupp
    co
    #
    @8
    ccnv
    cvv
    @2
    cdif
    #
    cima
    #
    cfn
    wph
    @8
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    @58
    @60
    wceq
    wph
    @10
    @61
    @11
    vx
    @3
    @7
    cvv
    mptexg
    syl
    c.0
    cW
    c0g
    cfv
    cvv
    sitgval.0
    cW
    c0g
    fvex
    eqeltri
    @8
    cvv
    cvv
    c.0
    suppimacnv
    sylancl
    wph
    @1
    cfn
    wcel
    @60
    @1
    wss
    @60
    cfn
    wcel
    wph
    cB
    cS
    c.x
    cF
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sibfmbl.1
    sibfrn
    @60
    @3
    @1
    @60
    @8
    cdm
    @3
    @8
    @59
    cnvimass
    vx
    @3
    @7
    @8
    @57
    dmmptss
    sstri
    @1
    @2
    difss
    sstri
    @1
    @60
    ssfi
    sylancl
    eqeltrd
    gsumcl2
    eqeltrd
end
