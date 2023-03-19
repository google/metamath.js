include "cv.mm"
include "crn.mm"
include "cxp.mm"
include "cop.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cresv.mm"
include "cslmd.mm"
include "ccnv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cin.mm"
include "csca.mm"
include "cress.mm"
include "cbs.mm"
include "adantr.mm"
include "cr.mm"
include "wfn.mm"
include "wss.mm"
include "simpl.mm"
include "wf.mm"
include "crrh.mm"
include "crrext.mm"
include "eqid.mm"
include "rrhfe.mm"
include "syl.mm"
include "feq1i.mm"
include "sylibr.mm"
include "ffn.mm"
include "rge0ssre.mm"
include "a1i.mm"
include "wne.mm"
include "wo.mm"
include "simpr.mm"
include "eldifad.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "wceq.mm"
include "wn.mm"
include "eldifbd.mm"
include "velsn.mm"
include "notbii.mm"
include "sylib.mm"
include "eqopi.mm"
include "ex.mm"
include "con3d.mm"
include "imp.mm"
include "syl2anc.mm"
include "ianor.mm"
include "df-ne.mm"
include "orbi12i.mm"
include "bitr4i.mm"
include "sibfinima.mm"
include "syl31anc.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "ressbas2.mm"
include "eleqtrd.mm"
include "cdm.mm"
include "cuni.mm"
include "sibff.mm"
include "ctps.mm"
include "wb.mm"
include "tpsuni.mm"
include "feq3.mm"
include "3syl.mm"
include "mpbird.mm"
include "sseldd.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "imaexg.mm"
include "resvbas.mm"
include "mp2b.mm"
include "resvsca.mm"
include "cvsca.mm"
include "resvvsca.mm"
include "slmdvscl.mm"

theorem sitgaddlemb
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vp: setvar p
  let vf: setvar f
  let vm: setvar m
  let vw: setvar w
  let vg: setvar g
  let vx: setvar x
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sitgadd.1: |- ( ph -> W e. TopSp )
  assume sitgadd.2: |- ( ph -> ( W |`v ( H " ( 0 [,) +oo ) ) ) e. SLMod )
  assume sitgadd.3: |- ( ph -> J e. Fre )
  assume sitgadd.4: |- ( ph -> F e. dom ( W sitg M ) )
  assume sitgadd.5: |- ( ph -> G e. dom ( W sitg M ) )
  assume sitgadd.6: |- ( ph -> ( Scalar ` W ) e. RRExt )
  assume sitgadd.7: |- .+ = ( +g ` W )


  assert |- ( ( ph /\ p e. ( ( ran F X. ran G ) \ { <. .0. , .0. >. } ) ) -> ( ( H ` ( M ` ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) ) ) .x. ( 2nd ` p ) ) e. B )

  proof
    wph
    vp
    cv
    #
    cF
    crn
    #
    cG
    crn
    #
    cxp
    #
    c.0
    c.0
    cop
    #
    csn
    #
    cdif
    wcel
    #
    wa
    #
    cW
    cH
    cc0
    cpnf
    cico
    co
    #
    cima
    #
    cresv
    co
    #
    cslmd
    wcel
    #
    cF
    ccnv
    @0
    c1st
    cfv
    #
    csn
    cima
    cG
    ccnv
    @0
    c2nd
    cfv
    #
    csn
    cima
    cin
    cM
    cfv
    #
    cH
    cfv
    #
    cW
    csca
    cfv
    #
    @9
    cress
    co
    #
    cbs
    cfv
    #
    wcel
    @13
    cB
    wcel
    @15
    @13
    c.x
    co
    cB
    wcel
    wph
    @11
    @6
    sitgadd.2
    adantr
    @7
    @15
    @9
    @18
    @7
    cH
    cr
    wfn
    #
    @8
    cr
    wss
    #
    @14
    @8
    wcel
    #
    @15
    @9
    wcel
    @7
    wph
    @19
    wph
    @6
    simpl
    #
    wph
    cr
    @16
    cbs
    cfv
    #
    cH
    wf
    #
    @19
    wph
    cr
    @23
    @16
    crrh
    cfv
    #
    wf
    #
    @24
    wph
    @16
    crrext
    wcel
    @26
    sitgadd.6
    @23
    @16
    @23
    eqid
    #
    rrhfe
    syl
    cr
    @23
    cH
    @25
    sitgval.h
    feq1i
    sylibr
    #
    cr
    @23
    cH
    ffn
    syl
    syl
    @20
    @7
    rge0ssre
    a1i
    @7
    wph
    @12
    @1
    wcel
    #
    @13
    @2
    wcel
    #
    @12
    c.0
    wne
    #
    @13
    c.0
    wne
    #
    wo
    #
    @21
    @22
    @7
    @0
    @3
    wcel
    #
    @29
    @7
    @0
    @3
    @5
    wph
    @6
    simpr
    #
    eldifad
    #
    @0
    @1
    @2
    xp1st
    syl
    @7
    @34
    @30
    @36
    @0
    @1
    @2
    xp2nd
    syl
    #
    @7
    @12
    c.0
    wceq
    #
    @13
    c.0
    wceq
    #
    wa
    #
    wn
    #
    @33
    @7
    @34
    @0
    @4
    wceq
    #
    wn
    #
    @41
    @36
    @7
    @0
    @5
    wcel
    #
    wn
    @43
    @7
    @0
    @3
    @5
    @35
    eldifbd
    @44
    @42
    vp
    @4
    velsn
    notbii
    sylib
    @34
    @43
    @41
    @34
    @40
    @42
    @34
    @40
    @42
    @0
    c.0
    c.0
    @1
    @2
    eqopi
    ex
    con3d
    imp
    syl2anc
    @41
    @38
    wn
    #
    @39
    wn
    #
    wo
    @33
    @38
    @39
    ianor
    @31
    @45
    @32
    @46
    @12
    c.0
    df-ne
    @13
    c.0
    df-ne
    orbi12i
    bitr4i
    sylib
    wph
    cB
    cS
    c.x
    cF
    cG
    cH
    cJ
    cM
    cV
    cW
    @12
    @13
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sitgadd.4
    sitgadd.5
    sitgadd.1
    sitgadd.3
    sibfinima
    syl31anc
    cr
    @8
    cH
    @14
    fnfvima
    syl3anc
    @7
    wph
    @9
    @18
    wceq
    #
    @22
    wph
    @9
    @23
    wss
    @47
    wph
    @9
    cH
    crn
    #
    @23
    cH
    @8
    imassrn
    wph
    @24
    @48
    @23
    wss
    @28
    cr
    @23
    cH
    frn
    syl
    syl5ss
    @9
    @23
    @17
    @16
    @17
    eqid
    @27
    ressbas2
    syl
    syl
    eleqtrd
    @7
    @2
    cB
    @13
    wph
    @2
    cB
    wss
    #
    @6
    wph
    cM
    cdm
    cuni
    #
    cB
    cG
    wf
    #
    @49
    wph
    @51
    @50
    cJ
    cuni
    #
    cG
    wf
    #
    wph
    cB
    cS
    c.x
    cG
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
    sitgadd.5
    sibff
    wph
    cW
    ctps
    wcel
    cB
    @52
    wceq
    @51
    @53
    wb
    sitgadd.1
    cB
    cJ
    cW
    sitgval.b
    sitgval.j
    tpsuni
    cB
    @52
    @50
    cG
    feq3
    3syl
    mpbird
    @50
    cB
    cG
    frn
    syl
    adantr
    @37
    sseldd
    @15
    c.x
    @17
    @18
    cB
    @10
    @13
    cH
    cvv
    wcel
    #
    @9
    cvv
    wcel
    #
    cB
    @10
    cbs
    cfv
    wceq
    cH
    @25
    cvv
    sitgval.h
    @16
    crrh
    fvex
    eqeltri
    #
    cH
    @8
    cvv
    imaexg
    #
    @9
    cB
    cW
    @10
    cvv
    @10
    eqid
    #
    sitgval.b
    resvbas
    mp2b
    @54
    @55
    @17
    @10
    csca
    cfv
    wceq
    @56
    @57
    @9
    @23
    @10
    @16
    cvv
    cW
    @58
    @16
    eqid
    @27
    resvsca
    mp2b
    @54
    @55
    c.x
    @10
    cvsca
    cfv
    wceq
    @56
    @57
    @9
    c.x
    cW
    @10
    cvv
    @58
    sitgval.x
    resvvsca
    mp2b
    @18
    eqid
    slmdvscl
    syl3anc
end
