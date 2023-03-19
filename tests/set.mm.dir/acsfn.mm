include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfn.mm"
include "cv.mm"
include "wi.mm"
include "cpw.mm"
include "crab.mm"
include "wceq.mm"
include "csn.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "cacs.mm"
include "cfv.mm"
include "ciun.mm"
include "wral.mm"
include "wfun.mm"
include "funmpt.mm"
include "funiunfv.mm"
include "mp1i.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "elpwi.mm"
include "sylan9ssr.mm"
include "selpw.mm"
include "sylibr.mm"
include "adantll.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "snex.mm"
include "0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "iuneq2dv.mm"
include "eqtr3d.mm"
include "sseq1d.mm"
include "iunss.mm"
include "wb.mm"
include "sseq1.mm"
include "bibi1d.mm"
include "snssg.mm"
include "adantr.mm"
include "biimt.mm"
include "adantl.mm"
include "bitr3d.mm"
include "wn.mm"
include "0ss.mm"
include "a1i.mm"
include "pm2.21.mm"
include "2thd.mm"
include "ifbothda.mm"
include "ralbidv.mm"
include "ad3antlr.mm"
include "syl5bb.mm"
include "sspwb.mm"
include "sylib.mm"
include "syl5ss.mm"
include "ralss.mm"
include "bi2.04.mm"
include "ralbii.mm"
include "elpwg.mm"
include "biimparc.mm"
include "ad2antlr.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "ceqsralv.mm"
include "vex.mm"
include "elpw2.mm"
include "simplrr.mm"
include "biantrud.mm"
include "elin.mm"
include "syl6bbr.mm"
include "syl5rbbr.mm"
include "3bitrd.mm"
include "3bitrrd.mm"
include "rabbidva.mm"
include "wf.mm"
include "simpll.mm"
include "snelpwi.mm"
include "0elpw.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fmptd.mm"
include "isacs1i.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem acsfn
  let cT: class T
  let cK: class K
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f

  disjoint K a
  disjoint T a
  disjoint V a
  disjoint X a
  disjoint K b
  disjoint K c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint T b
  disjoint T c
  disjoint V b
  disjoint V c
  disjoint X b
  disjoint X c
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a d
  disjoint a e
  disjoint d e
  disjoint a f
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint e x
  assert |- ( ( ( X e. V /\ K e. X ) /\ ( T C_ X /\ T e. Fin ) ) -> { a e. ~P X | ( T C_ a -> K e. a ) } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    #
    cK
    cX
    wcel
    #
    wa
    #
    cT
    cX
    wss
    #
    cT
    cfn
    wcel
    #
    wa
    #
    wa
    #
    cT
    va
    cv
    #
    wss
    #
    cK
    @7
    wcel
    #
    wi
    #
    va
    cX
    cpw
    #
    crab
    vb
    @11
    vb
    cv
    #
    cT
    wceq
    #
    cK
    csn
    #
    c0
    cif
    #
    cmpt
    #
    @7
    cpw
    #
    cfn
    cin
    #
    cima
    cuni
    #
    @7
    wss
    #
    va
    @11
    crab
    #
    cX
    cacs
    cfv
    #
    @6
    @10
    @20
    va
    @11
    @6
    @7
    @11
    wcel
    #
    wa
    #
    @20
    vc
    @18
    vc
    cv
    #
    cT
    wceq
    #
    @14
    c0
    cif
    #
    ciun
    #
    @7
    wss
    #
    @26
    @9
    wi
    #
    vc
    @18
    wral
    #
    @10
    @24
    @19
    @28
    @7
    @24
    vc
    @18
    @25
    @16
    cfv
    #
    ciun
    #
    @19
    @28
    @16
    wfun
    @33
    @19
    wceq
    @24
    vb
    @11
    @15
    funmpt
    vc
    @18
    @16
    funiunfv
    mp1i
    @24
    vc
    @18
    @32
    @27
    @24
    @25
    @18
    wcel
    #
    wa
    @25
    @11
    wcel
    #
    @32
    @27
    wceq
    @23
    @34
    @35
    @6
    @23
    @34
    wa
    @25
    cX
    wss
    @35
    @34
    @23
    @25
    @7
    cX
    @34
    @25
    @7
    @18
    @17
    @25
    @17
    cfn
    inss1
    #
    sseli
    elpwid
    @7
    cX
    elpwi
    #
    sylan9ssr
    vc
    cX
    selpw
    sylibr
    adantll
    vb
    @25
    @15
    @27
    @11
    @16
    vb
    vc
    weq
    @13
    @26
    @14
    c0
    @12
    @25
    cT
    eqeq1
    ifbid
    @16
    eqid
    #
    @26
    @14
    c0
    cK
    snex
    0ex
    ifex
    fvmpt
    syl
    iuneq2dv
    eqtr3d
    sseq1d
    @29
    @27
    @7
    wss
    #
    vc
    @18
    wral
    #
    @24
    @31
    vc
    @18
    @27
    @7
    iunss
    @1
    @40
    @31
    wb
    @0
    @5
    @23
    @1
    @39
    @30
    vc
    @18
    @26
    @14
    @7
    wss
    #
    @30
    wb
    c0
    @7
    wss
    #
    @30
    wb
    #
    @39
    @30
    wb
    @1
    @14
    c0
    @14
    @27
    wceq
    @41
    @39
    @30
    @14
    @27
    @7
    sseq1
    bibi1d
    c0
    @27
    wceq
    @42
    @39
    @30
    c0
    @27
    @7
    sseq1
    bibi1d
    @1
    @26
    wa
    @9
    @41
    @30
    @1
    @9
    @41
    wb
    @26
    cK
    @7
    cX
    snssg
    adantr
    @26
    @9
    @30
    wb
    @1
    @26
    @9
    biimt
    adantl
    bitr3d
    @26
    wn
    #
    @43
    @1
    @44
    @42
    @30
    @42
    @44
    @7
    0ss
    a1i
    @26
    @9
    pm2.21
    2thd
    adantl
    ifbothda
    ralbidv
    ad3antlr
    syl5bb
    @24
    @31
    @34
    @30
    wi
    #
    vc
    @11
    wral
    #
    cT
    @18
    wcel
    #
    @9
    wi
    #
    @10
    @24
    @18
    @11
    wss
    #
    @31
    @46
    wb
    @23
    @49
    @6
    @23
    @18
    @17
    @11
    @36
    @23
    @7
    cX
    wss
    @17
    @11
    wss
    @37
    @7
    cX
    sspwb
    sylib
    syl5ss
    adantl
    @30
    vc
    @18
    @11
    ralss
    syl
    @46
    @26
    @34
    @9
    wi
    #
    wi
    #
    vc
    @11
    wral
    #
    @24
    @48
    @45
    @51
    vc
    @11
    @34
    @26
    @9
    bi2.04
    ralbii
    @24
    cT
    @11
    wcel
    #
    @52
    @48
    wb
    @5
    @53
    @2
    @23
    @4
    @53
    @3
    cT
    cX
    cfn
    elpwg
    biimparc
    ad2antlr
    @50
    @48
    vc
    cT
    @11
    @26
    @34
    @47
    @9
    @25
    cT
    @18
    eleq1
    imbi1d
    ceqsralv
    syl
    syl5bb
    @24
    @47
    @8
    @9
    @8
    cT
    @17
    wcel
    #
    @24
    @47
    cT
    @7
    va
    vex
    elpw2
    @24
    @54
    @54
    @4
    wa
    @47
    @24
    @4
    @54
    @2
    @3
    @4
    @23
    simplrr
    biantrud
    cT
    @17
    cfn
    elin
    syl6bbr
    syl5rbbr
    imbi1d
    3bitrd
    3bitrrd
    rabbidva
    @6
    @0
    @11
    @11
    @16
    wf
    @21
    @22
    wcel
    @0
    @1
    @5
    simpll
    @6
    vb
    @11
    @15
    @11
    @16
    @6
    @15
    @11
    wcel
    #
    @12
    @11
    wcel
    @6
    @14
    @11
    wcel
    #
    c0
    @11
    wcel
    @55
    @1
    @56
    @0
    @5
    cK
    cX
    snelpwi
    ad2antlr
    cX
    0elpw
    @13
    @14
    c0
    @11
    ifcl
    sylancl
    adantr
    @38
    fmptd
    @16
    cV
    cX
    va
    isacs1i
    syl2anc
    eqeltrd
end
