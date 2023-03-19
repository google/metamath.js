include "cress.mm"
include "co.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cresc.mm"
include "cvv.mm"
include "eqid.mm"
include "ovexd.mm"
include "ssexd.mm"
include "rescval2.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "simpr.mm"
include "adantr.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "1re.mm"
include "1nn.mm"
include "4nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "ltneii.mm"
include "basendx.mm"
include "homndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "ressid2.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "ovex.mm"
include "cxp.mm"
include "wfn.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "fnex.mm"
include "setsabs.mm"
include "sylancr.mm"
include "cin.mm"
include "ressbas.mm"
include "syl.mm"
include "sseq1d.mm"
include "biimpar.mm"
include "inss2.mm"
include "a1i.mm"
include "ssind.mm"
include "ssrin.mm"
include "eqssd.mm"
include "oveq2d.mm"
include "ressinbas.mm"
include "3eqtr4d.mm"
include "3eqtrd.mm"
include "wn.mm"
include "ressval2.mm"
include "necomi.mm"
include "fvex.mm"
include "inex2.mm"
include "setscom.mm"
include "syl22anc.mm"
include "ressabs.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"

theorem rescabs
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cH: class H
  let cJ: class J
  let cV: class V
  let cW: class W
  assume rescabs.c: |- ( ph -> C e. V )
  assume rescabs.h: |- ( ph -> H Fn ( S X. S ) )
  assume rescabs.j: |- ( ph -> J Fn ( T X. T ) )
  assume rescabs.s: |- ( ph -> S e. W )
  assume rescabs.t: |- ( ph -> T C_ S )


  assert |- ( ph -> ( ( C |`cat H ) |`cat J ) = ( C |`cat J ) )

  proof
    wph
    cC
    cS
    cress
    co
    #
    cnx
    chom
    cfv
    #
    cH
    cop
    #
    csts
    co
    #
    cJ
    cresc
    co
    #
    cC
    cT
    cress
    co
    #
    @1
    cJ
    cop
    #
    csts
    co
    #
    cC
    cH
    cresc
    co
    #
    cJ
    cresc
    co
    cC
    cJ
    cresc
    co
    #
    wph
    @4
    @3
    cT
    cress
    co
    #
    @6
    csts
    co
    #
    @7
    wph
    @3
    @4
    cT
    cJ
    cvv
    cvv
    @4
    eqid
    wph
    @0
    @2
    csts
    ovexd
    wph
    cT
    cS
    cW
    rescabs.s
    rescabs.t
    ssexd
    #
    rescabs.j
    rescval2
    wph
    @0
    cbs
    cfv
    #
    cT
    wss
    #
    @11
    @7
    wceq
    wph
    @14
    wa
    #
    @11
    @3
    @6
    csts
    co
    #
    @0
    @6
    csts
    co
    #
    @7
    @15
    @10
    @3
    @6
    csts
    @15
    @14
    @3
    cvv
    wcel
    #
    cT
    cvv
    wcel
    #
    @10
    @3
    wceq
    wph
    @14
    simpr
    @15
    @0
    @2
    csts
    ovexd
    wph
    @19
    @14
    @12
    adantr
    #
    cT
    @13
    @10
    @3
    cvv
    cvv
    @10
    eqid
    #
    cH
    @1
    cbs
    @0
    baseid
    cnx
    cbs
    cfv
    #
    @1
    wne
    c1
    c1
    c4
    cdc
    #
    wne
    c1
    @23
    1re
    c1
    c4
    c1
    1nn
    4nn0
    1nn0
    1lt10
    declti
    ltneii
    @22
    c1
    @1
    @23
    basendx
    homndx
    neeq12i
    mpbir
    #
    setsnid
    #
    ressid2
    syl3anc
    oveq1d
    @15
    @0
    cvv
    wcel
    #
    cJ
    cvv
    wcel
    #
    @16
    @17
    wceq
    cC
    cS
    cress
    ovex
    wph
    @27
    @14
    wph
    cJ
    cT
    cT
    cxp
    #
    wfn
    @28
    cvv
    wcel
    #
    @27
    rescabs.j
    wph
    @19
    @19
    @29
    @12
    @12
    cT
    cT
    cvv
    cvv
    xpexg
    syl2anc
    @28
    cvv
    cJ
    fnex
    syl2anc
    #
    adantr
    @1
    cH
    cJ
    @0
    cvv
    cvv
    setsabs
    sylancr
    @15
    @0
    @5
    @6
    csts
    @15
    cC
    cS
    cC
    cbs
    cfv
    #
    cin
    #
    cress
    co
    #
    cC
    cT
    @31
    cin
    #
    cress
    co
    #
    @0
    @5
    @15
    @32
    @34
    cC
    cress
    @15
    @32
    @34
    @15
    @32
    cT
    @31
    wph
    @32
    cT
    wss
    @14
    wph
    @32
    @13
    cT
    wph
    cS
    cW
    wcel
    #
    @32
    @13
    wceq
    rescabs.s
    cS
    @31
    @0
    cW
    cC
    @0
    eqid
    @31
    eqid
    #
    ressbas
    syl
    sseq1d
    biimpar
    @32
    @31
    wss
    @15
    cS
    @31
    inss2
    a1i
    ssind
    @15
    cT
    cS
    wss
    #
    @34
    @32
    wss
    wph
    @38
    @14
    rescabs.t
    adantr
    cT
    cS
    @31
    ssrin
    syl
    eqssd
    oveq2d
    @15
    @36
    @0
    @33
    wceq
    wph
    @36
    @14
    rescabs.s
    adantr
    cS
    @31
    cC
    cW
    @37
    ressinbas
    syl
    @15
    @19
    @5
    @35
    wceq
    @20
    cT
    @31
    cC
    cvv
    @37
    ressinbas
    syl
    3eqtr4d
    oveq1d
    3eqtrd
    wph
    @14
    wn
    #
    wa
    #
    @11
    @5
    @2
    csts
    co
    #
    @6
    csts
    co
    #
    @7
    @40
    @10
    @41
    @6
    csts
    @40
    @10
    @3
    @22
    cT
    @13
    cin
    #
    cop
    #
    csts
    co
    #
    @0
    @44
    csts
    co
    #
    @2
    csts
    co
    #
    @41
    @40
    @39
    @18
    @19
    @10
    @45
    wceq
    wph
    @39
    simpr
    #
    @40
    @0
    @2
    csts
    ovexd
    wph
    @19
    @39
    @12
    adantr
    #
    cT
    @13
    @10
    @3
    cvv
    cvv
    @21
    @25
    ressval2
    syl3anc
    @40
    @26
    @1
    @22
    wne
    #
    cH
    cvv
    wcel
    #
    @43
    cvv
    wcel
    #
    @45
    @47
    wceq
    @40
    cC
    cS
    cress
    ovexd
    #
    @50
    @40
    @22
    @1
    @24
    necomi
    a1i
    wph
    @51
    @39
    wph
    cH
    cS
    cS
    cxp
    #
    wfn
    @54
    cvv
    wcel
    #
    @51
    rescabs.h
    wph
    @36
    @36
    @55
    rescabs.s
    rescabs.s
    cS
    cS
    cW
    cW
    xpexg
    syl2anc
    @54
    cvv
    cH
    fnex
    syl2anc
    adantr
    @52
    @40
    @13
    cT
    @0
    cbs
    fvex
    inex2
    a1i
    @1
    @22
    cH
    @43
    @0
    cvv
    cvv
    cvv
    cnx
    chom
    fvex
    cnx
    cbs
    fvex
    setscom
    syl22anc
    @40
    @46
    @5
    @2
    csts
    @40
    @0
    cT
    cress
    co
    #
    @46
    @5
    @40
    @39
    @26
    @19
    @56
    @46
    wceq
    @48
    @53
    @49
    cT
    @13
    @56
    @0
    cvv
    cvv
    @56
    eqid
    @13
    eqid
    ressval2
    syl3anc
    @40
    @36
    @38
    @56
    @5
    wceq
    wph
    @36
    @39
    rescabs.s
    adantr
    wph
    @38
    @39
    rescabs.t
    adantr
    cS
    cT
    cC
    cW
    ressabs
    syl2anc
    eqtr3d
    oveq1d
    3eqtrd
    oveq1d
    @40
    @5
    cvv
    wcel
    @27
    @42
    @7
    wceq
    cC
    cT
    cress
    ovex
    wph
    @27
    @39
    @30
    adantr
    @1
    cH
    cJ
    @5
    cvv
    cvv
    setsabs
    sylancr
    eqtrd
    pm2.61dan
    eqtrd
    wph
    @8
    @3
    cJ
    cresc
    wph
    cC
    @8
    cS
    cH
    cV
    cW
    @8
    eqid
    rescabs.c
    rescabs.s
    rescabs.h
    rescval2
    oveq1d
    wph
    cC
    @9
    cT
    cJ
    cV
    cvv
    @9
    eqid
    rescabs.c
    @12
    rescabs.j
    rescval2
    3eqtr4d
end
