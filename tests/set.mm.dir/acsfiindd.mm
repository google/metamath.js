include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "cmre.mm"
include "cfv.mm"
include "acsmred.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "elpwid.mm"
include "mrissmrid.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "cun.mm"
include "elfpw.mm"
include "sylib.mm"
include "simpld.mm"
include "difss2d.mm"
include "snssd.mm"
include "unssd.mm"
include "simprd.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "ad4antr.mm"
include "simpllr.mm"
include "snidg.mm"
include "elun2.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "ismri2dad.mm"
include "wi.mm"
include "ad3antrrr.mm"
include "neldifsnd.mm"
include "ssneldd.mm"
include "difsnb.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "ssdifd.mm"
include "eqsstr3d.mm"
include "sstrd.mm"
include "eqsstrd.mm"
include "ssdifssd.mm"
include "mrcssd.mm"
include "sseld.mm"
include "mtod.mm"
include "ex.mm"
include "rspcimdv.mm"
include "syl5bi.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "wb.mm"
include "wrex.mm"
include "acsficl2d.mm"
include "notbid.mm"
include "ralnex.mm"
include "syl6bbr.mm"
include "mpbird.mm"
include "an32s.mm"
include "ismri2dd.mm"
include "impbida.mm"

theorem acsfiindd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vs: setvar s
  let vt: setvar t
  assume acsfiindd.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsfiindd.2: |- N = ( mrCls ` A )
  assume acsfiindd.3: |- I = ( mrInd ` A )
  assume acsfiindd.4: |- ( ph -> S C_ X )


  assert |- ( ph -> ( S e. I <-> ( ~P S i^i Fin ) C_ I ) )

  proof
    wph
    cS
    cI
    wcel
    #
    cS
    cpw
    #
    cfn
    cin
    #
    cI
    wss
    #
    wph
    @0
    wa
    #
    vs
    cv
    #
    cI
    wcel
    #
    vs
    @2
    wral
    #
    @3
    @4
    @6
    vs
    @2
    @4
    @5
    @2
    wcel
    #
    wa
    #
    cA
    cS
    @5
    cI
    cN
    cX
    wph
    cA
    cX
    cmre
    cfv
    wcel
    #
    @0
    @8
    wph
    cA
    cX
    acsfiindd.1
    acsmred
    #
    ad2antrr
    acsfiindd.2
    acsfiindd.3
    wph
    @0
    @8
    simplr
    @9
    @5
    cS
    @9
    @2
    @1
    @5
    @1
    cfn
    inss1
    @4
    @8
    simpr
    sseldi
    elpwid
    mrissmrid
    ralrimiva
    vs
    @2
    cI
    dfss3
    #
    sylibr
    wph
    @3
    wa
    #
    vx
    cA
    cS
    cI
    cN
    cX
    acsfiindd.2
    acsfiindd.3
    wph
    @10
    @3
    @11
    adantr
    wph
    cS
    cX
    wss
    #
    @3
    acsfiindd.4
    adantr
    @13
    vx
    cv
    #
    cS
    @15
    csn
    #
    cdif
    #
    cN
    cfv
    wcel
    #
    wn
    #
    vx
    cS
    wph
    @15
    cS
    wcel
    #
    @3
    @19
    wph
    @20
    wa
    #
    @3
    wa
    #
    @19
    @15
    vt
    cv
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vt
    @17
    cpw
    cfn
    cin
    #
    wral
    #
    @22
    @26
    vt
    @27
    @21
    @23
    @27
    wcel
    #
    @3
    @26
    @3
    @7
    @21
    @29
    wa
    #
    @26
    @12
    @30
    @6
    @26
    vs
    @23
    @16
    cun
    #
    @2
    @30
    @31
    cS
    wss
    #
    @31
    cfn
    wcel
    #
    @31
    @2
    wcel
    @30
    @23
    @16
    cS
    @30
    @23
    cS
    @16
    @30
    @23
    @17
    wss
    #
    @23
    cfn
    wcel
    #
    @30
    @29
    @34
    @35
    wa
    @21
    @29
    simpr
    @23
    @17
    elfpw
    sylib
    #
    simpld
    #
    difss2d
    @30
    @15
    cS
    wph
    @20
    @29
    simplr
    snssd
    unssd
    #
    @30
    @35
    @16
    cfn
    wcel
    @33
    @30
    @34
    @35
    @36
    simprd
    @15
    snfi
    @23
    @16
    unfi
    sylancl
    @31
    cS
    elfpw
    sylanbrc
    @30
    @5
    @31
    wceq
    #
    wa
    #
    @6
    @26
    @40
    @6
    wa
    #
    @25
    @15
    @5
    @16
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    @41
    cA
    @5
    cI
    cN
    cX
    @15
    acsfiindd.2
    acsfiindd.3
    wph
    @10
    @20
    @29
    @39
    @6
    @11
    ad4antr
    @40
    @6
    simpr
    @40
    @15
    @5
    wcel
    @6
    @40
    @15
    @31
    @5
    @40
    @20
    @15
    @16
    wcel
    @15
    @31
    wcel
    wph
    @20
    @29
    @39
    simpllr
    @15
    cS
    snidg
    @15
    @16
    @23
    elun2
    3syl
    @30
    @39
    simpr
    #
    eleqtrrd
    adantr
    ismri2dad
    @40
    @25
    @44
    wi
    @6
    @40
    @24
    @43
    @15
    @40
    cA
    @23
    cN
    @42
    cX
    wph
    @10
    @20
    @29
    @39
    @11
    ad3antrrr
    acsfiindd.2
    @40
    @23
    @23
    @16
    cdif
    #
    @42
    @40
    @15
    @23
    wcel
    wn
    @46
    @23
    wceq
    @40
    @23
    @17
    @15
    @30
    @34
    @39
    @37
    adantr
    @40
    @15
    cS
    neldifsnd
    ssneldd
    @15
    @23
    difsnb
    sylib
    @40
    @23
    @5
    @16
    @40
    @31
    @23
    @5
    @23
    @16
    ssun1
    @45
    syl5sseqr
    ssdifd
    eqsstr3d
    @40
    @5
    cX
    @16
    @40
    @5
    @31
    cX
    @45
    @40
    @31
    cS
    cX
    @30
    @32
    @39
    @38
    adantr
    wph
    @14
    @20
    @29
    @39
    acsfiindd.4
    ad3antrrr
    sstrd
    eqsstrd
    ssdifssd
    mrcssd
    sseld
    adantr
    mtod
    ex
    rspcimdv
    syl5bi
    impancom
    ralrimiv
    wph
    @19
    @28
    wb
    @20
    @3
    wph
    @19
    @25
    vt
    @27
    wrex
    #
    wn
    @28
    wph
    @18
    @47
    wph
    vt
    cA
    @17
    cN
    cX
    @15
    acsfiindd.1
    acsfiindd.2
    wph
    cS
    cX
    @16
    acsfiindd.4
    ssdifssd
    acsficl2d
    notbid
    @25
    vt
    @27
    ralnex
    syl6bbr
    ad2antrr
    mpbird
    an32s
    ralrimiva
    ismri2dd
    impbida
end
