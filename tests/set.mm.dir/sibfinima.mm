include "crn.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wo.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "clt.mm"
include "cico.mm"
include "co.mm"
include "cxr.mm"
include "cicc.mm"
include "cdm.mm"
include "cmeas.mm"
include "cuni.mm"
include "measbasedom.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "csiga.mm"
include "dmmeas.mm"
include "syl.mm"
include "csigagen.mm"
include "ct1.mm"
include "sgsiga.mm"
include "syl5eqel.mm"
include "cmbfm.mm"
include "sibfmbl.mm"
include "ccld.mm"
include "wss.mm"
include "ctps.mm"
include "ctop.mm"
include "tpstop.mm"
include "cldssbrsiga.mm"
include "3syl.mm"
include "syl6sseqr.mm"
include "wf.mm"
include "sibff.mm"
include "frn.mm"
include "simp2.mm"
include "sseldd.mm"
include "eqid.mm"
include "t1sncld.mm"
include "syl2anc.mm"
include "mbfmcnvima.mm"
include "simp3.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "measvxrge0.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "adantr.mm"
include "0re.mm"
include "a1i.mm"
include "simprbi.mm"
include "pnfxr.mm"
include "inss1.mm"
include "measssd.mm"
include "cdif.mm"
include "simpl1.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "sibfima.mm"
include "wb.mm"
include "elico2.mm"
include "mp2an.mm"
include "simp3bi.mm"
include "xrlelttrd.mm"
include "inss2.mm"
include "jaodan.mm"
include "xrre3.mm"
include "syl22anc.mm"
include "syl3anbrc.mm"

theorem sibfinima
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cA: class A
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
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
  assume sibfinima.g: |- ( ph -> G e. dom ( W sitg M ) )
  assume sibfinima.w: |- ( ph -> W e. TopSp )
  assume sibfinima.j: |- ( ph -> J e. Fre )


  assert |- ( ( ( ph /\ X e. ran F /\ Y e. ran G ) /\ ( X =/= .0. \/ Y =/= .0. ) ) -> ( M ` ( ( `' F " { X } ) i^i ( `' G " { Y } ) ) ) e. ( 0 [,) +oo ) )

  proof
    wph
    cX
    cF
    crn
    #
    wcel
    #
    cY
    cG
    crn
    #
    wcel
    #
    w3a
    #
    cX
    c.0
    wne
    #
    cY
    c.0
    wne
    #
    wo
    #
    wa
    #
    cF
    ccnv
    cX
    csn
    #
    cima
    #
    cG
    ccnv
    cY
    csn
    #
    cima
    #
    cin
    #
    cM
    cfv
    #
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @14
    cpnf
    clt
    wbr
    #
    @14
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @8
    @14
    cxr
    wcel
    #
    cc0
    cr
    wcel
    #
    @16
    @17
    @15
    @4
    @20
    @7
    @4
    @14
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @20
    @4
    cM
    cM
    cdm
    #
    cmeas
    cfv
    wcel
    #
    @13
    @24
    wcel
    #
    @23
    wph
    @1
    @25
    @3
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    #
    @25
    sitgval.2
    cM
    measbasedom
    sylib
    3ad2ant1
    #
    @4
    @24
    csiga
    crn
    cuni
    #
    wcel
    #
    @10
    @24
    wcel
    #
    @12
    @24
    wcel
    #
    @26
    wph
    @1
    @30
    @3
    wph
    @27
    @30
    sitgval.2
    cM
    dmmeas
    syl
    3ad2ant1
    #
    @4
    @9
    @24
    cS
    cF
    @33
    wph
    @1
    cS
    @29
    wcel
    @3
    wph
    cS
    cJ
    csigagen
    cfv
    #
    @29
    sitgval.s
    wph
    cJ
    ct1
    sibfinima.j
    sgsiga
    syl5eqel
    3ad2ant1
    #
    wph
    @1
    cF
    @24
    cS
    cmbfm
    co
    #
    wcel
    @3
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
    3ad2ant1
    @4
    cJ
    ccld
    cfv
    #
    cS
    @9
    wph
    @1
    @37
    cS
    wss
    @3
    wph
    @37
    @34
    cS
    wph
    cW
    ctps
    wcel
    cJ
    ctop
    wcel
    @37
    @34
    wss
    sibfinima.w
    cJ
    cW
    sitgval.j
    tpstop
    cJ
    cldssbrsiga
    3syl
    sitgval.s
    syl6sseqr
    3ad2ant1
    #
    @4
    cJ
    ct1
    wcel
    #
    cX
    cJ
    cuni
    #
    wcel
    @9
    @37
    wcel
    wph
    @1
    @39
    @3
    sibfinima.j
    3ad2ant1
    #
    @4
    @0
    @40
    cX
    wph
    @1
    @0
    @40
    wss
    #
    @3
    wph
    @24
    cuni
    #
    @40
    cF
    wf
    @42
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
    sibff
    @43
    @40
    cF
    frn
    syl
    3ad2ant1
    wph
    @1
    @3
    simp2
    #
    sseldd
    cX
    cJ
    @40
    @40
    eqid
    #
    t1sncld
    syl2anc
    sseldd
    mbfmcnvima
    #
    @4
    @11
    @24
    cS
    cG
    @33
    @35
    wph
    @1
    cG
    @36
    wcel
    @3
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
    sibfinima.g
    sibfmbl
    3ad2ant1
    @4
    @37
    cS
    @11
    @38
    @4
    @39
    cY
    @40
    wcel
    @11
    @37
    wcel
    @41
    @4
    @2
    @40
    cY
    wph
    @1
    @2
    @40
    wss
    #
    @3
    wph
    @43
    @40
    cG
    wf
    @47
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
    sibfinima.g
    sibff
    @43
    @40
    cG
    frn
    syl
    3ad2ant1
    wph
    @1
    @3
    simp3
    #
    sseldd
    cY
    cJ
    @40
    @45
    t1sncld
    syl2anc
    sseldd
    mbfmcnvima
    #
    @10
    @12
    @24
    inelsiga
    syl3anc
    #
    @13
    @24
    cM
    measvxrge0
    syl2anc
    #
    @23
    @20
    @16
    @14
    elxrge0
    #
    simplbi
    syl
    #
    adantr
    @21
    @8
    0re
    a1i
    @4
    @16
    @7
    @4
    @23
    @16
    @51
    @23
    @20
    @16
    @52
    simprbi
    syl
    adantr
    #
    @4
    @5
    @17
    @6
    @4
    @5
    wa
    #
    @14
    @10
    cM
    cfv
    #
    cpnf
    @4
    @20
    @5
    @53
    adantr
    @55
    @56
    @22
    wcel
    #
    @56
    cxr
    wcel
    #
    @55
    @25
    @31
    @57
    @4
    @25
    @5
    @28
    adantr
    #
    @4
    @31
    @5
    @46
    adantr
    #
    @10
    @24
    cM
    measvxrge0
    syl2anc
    @57
    @58
    cc0
    @56
    cle
    wbr
    #
    @56
    elxrge0
    simplbi
    syl
    cpnf
    cxr
    wcel
    #
    @55
    pnfxr
    a1i
    @55
    @13
    @10
    @24
    cM
    @59
    @4
    @26
    @5
    @50
    adantr
    @60
    @13
    @10
    wss
    @55
    @10
    @12
    inss1
    a1i
    measssd
    @55
    @56
    @18
    wcel
    #
    @56
    cpnf
    clt
    wbr
    #
    @55
    wph
    cX
    @0
    c.0
    csn
    #
    cdif
    wcel
    #
    @63
    wph
    @1
    @3
    @5
    simpl1
    @55
    @1
    @5
    wa
    @66
    @4
    @1
    @5
    @44
    anim1i
    cX
    @0
    c.0
    eldifsn
    sylibr
    wph
    cX
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
    syl2anc
    @63
    @56
    cr
    wcel
    #
    @61
    @64
    @21
    @62
    @63
    @67
    @61
    @64
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    @56
    elico2
    mp2an
    simp3bi
    syl
    xrlelttrd
    @4
    @6
    wa
    #
    @14
    @12
    cM
    cfv
    #
    cpnf
    @4
    @20
    @6
    @53
    adantr
    @68
    @69
    @22
    wcel
    #
    @69
    cxr
    wcel
    #
    @68
    @25
    @32
    @70
    @4
    @25
    @6
    @28
    adantr
    #
    @4
    @32
    @6
    @49
    adantr
    #
    @12
    @24
    cM
    measvxrge0
    syl2anc
    @70
    @71
    cc0
    @69
    cle
    wbr
    #
    @69
    elxrge0
    simplbi
    syl
    @62
    @68
    pnfxr
    a1i
    @68
    @13
    @12
    @24
    cM
    @72
    @4
    @26
    @6
    @50
    adantr
    @73
    @13
    @12
    wss
    @68
    @10
    @12
    inss2
    a1i
    measssd
    @68
    @69
    @18
    wcel
    #
    @69
    cpnf
    clt
    wbr
    #
    @68
    wph
    cY
    @2
    @65
    cdif
    wcel
    #
    @75
    wph
    @1
    @3
    @6
    simpl1
    @68
    @3
    @6
    wa
    @77
    @4
    @3
    @6
    @48
    anim1i
    cY
    @2
    c.0
    eldifsn
    sylibr
    wph
    cY
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
    sibfinima.g
    sibfima
    syl2anc
    @75
    @69
    cr
    wcel
    #
    @74
    @76
    @21
    @62
    @75
    @78
    @74
    @76
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    @69
    elico2
    mp2an
    simp3bi
    syl
    xrlelttrd
    jaodan
    #
    @14
    cc0
    xrre3
    syl22anc
    @54
    @79
    @21
    @62
    @19
    @15
    @16
    @17
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    @14
    elico2
    mp2an
    syl3anbrc
end
