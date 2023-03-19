include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cv.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "acsmre.mm"
include "wa.mm"
include "wss.mm"
include "cmrc.mm"
include "cfn.mm"
include "cin.mm"
include "mresspw.mm"
include "syl.mm"
include "sspwb.mm"
include "sylib.mm"
include "sselda.mm"
include "elpwid.mm"
include "sspwuni.mm"
include "adantr.mm"
include "wrex.mm"
include "inss1.mm"
include "sseli.mm"
include "inss2.mm"
include "fissuni.mm"
include "syl2anc.mm"
include "ad2antll.mm"
include "ad3antrrr.mm"
include "eqid.mm"
include "simprr.mm"
include "unissd.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "sstrd.mm"
include "mrcssd.mm"
include "simpl.mm"
include "adantl.mm"
include "ipodrsfi.mm"
include "syl3anc.mm"
include "wel.mm"
include "elpwi.mm"
include "simprl.mm"
include "sseldd.mm"
include "mrcsscl.mm"
include "elssuni.mm"
include "rexlimddv.mm"
include "anassrs.mm"
include "adantrr.mm"
include "adantlrr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "acsfiel.mm"
include "mpbir2and.mm"
include "ex.mm"
include "jca.mm"

theorem isacs3lem
  let cC: class C
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cY: class Y
  let cS: class S

  disjoint C s
  disjoint X s
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint F s
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y t
  disjoint S s
  assert |- ( C e. ( ACS ` X ) -> ( C e. ( Moore ` X ) /\ A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. C ) ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    #
    cC
    cX
    cmre
    cfv
    wcel
    #
    vs
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    #
    @2
    cuni
    #
    cC
    wcel
    #
    wi
    #
    vs
    cC
    cpw
    #
    wral
    cC
    cX
    acsmre
    #
    @0
    @6
    vs
    @7
    @0
    @2
    @7
    wcel
    #
    wa
    #
    @3
    @5
    @10
    @3
    wa
    #
    @5
    @4
    cX
    wss
    #
    vx
    cv
    #
    cC
    cmrc
    cfv
    #
    cfv
    #
    @4
    wss
    #
    vx
    @4
    cpw
    #
    cfn
    cin
    #
    wral
    #
    @10
    @12
    @3
    @10
    @2
    cX
    cpw
    #
    wss
    @12
    @10
    @2
    @20
    @0
    @7
    @20
    cpw
    #
    @2
    @0
    cC
    @20
    wss
    #
    @7
    @21
    wss
    @0
    @1
    @22
    @8
    cC
    cX
    mresspw
    syl
    cC
    @20
    sspwb
    sylib
    sselda
    elpwid
    @2
    cX
    sspwuni
    sylib
    #
    adantr
    @11
    @16
    vx
    @18
    @10
    @3
    @13
    @18
    wcel
    #
    @16
    @10
    @3
    @24
    wa
    #
    wa
    #
    @13
    vy
    cv
    #
    cuni
    #
    wss
    #
    @16
    vy
    @2
    cpw
    #
    cfn
    cin
    #
    @24
    @29
    vy
    @31
    wrex
    #
    @10
    @3
    @24
    @13
    @4
    wss
    #
    @13
    cfn
    wcel
    @32
    @24
    @13
    @4
    @18
    @17
    @13
    @17
    cfn
    inss1
    sseli
    elpwid
    @18
    cfn
    @13
    @17
    cfn
    inss2
    sseli
    @13
    @2
    vy
    fissuni
    syl2anc
    ad2antll
    @26
    @27
    @31
    wcel
    #
    @29
    wa
    #
    wa
    #
    @15
    @28
    @14
    cfv
    #
    @4
    @36
    cC
    @13
    @14
    @28
    cX
    @0
    @1
    @9
    @25
    @35
    @8
    ad3antrrr
    @14
    eqid
    #
    @26
    @34
    @29
    simprr
    @36
    @28
    @4
    cX
    @34
    @28
    @4
    wss
    @26
    @29
    @34
    @27
    @2
    @34
    @27
    @2
    @31
    @30
    @27
    @30
    cfn
    inss1
    sseli
    elpwid
    #
    unissd
    ad2antrl
    @10
    @12
    @25
    @35
    @23
    ad2antrr
    sstrd
    mrcssd
    @10
    @3
    @35
    @37
    @4
    wss
    #
    @24
    @11
    @34
    @40
    @29
    @10
    @3
    @34
    @40
    @10
    @3
    @34
    wa
    #
    wa
    #
    @28
    @13
    wss
    #
    @40
    vx
    @2
    @41
    @43
    vx
    @2
    wrex
    #
    @10
    @41
    @3
    @27
    @2
    wss
    #
    @27
    cfn
    wcel
    #
    @44
    @3
    @34
    simpl
    @34
    @45
    @3
    @39
    adantl
    @34
    @46
    @3
    @31
    cfn
    @27
    @30
    cfn
    inss2
    sseli
    adantl
    vx
    @2
    @27
    ipodrsfi
    syl3anc
    adantl
    @42
    vx
    vs
    wel
    #
    @43
    wa
    #
    wa
    #
    @37
    @13
    @4
    @49
    @1
    @43
    @13
    cC
    wcel
    @37
    @13
    wss
    @0
    @1
    @9
    @41
    @48
    @8
    ad3antrrr
    @42
    @47
    @43
    simprr
    @49
    @2
    cC
    @13
    @10
    @2
    cC
    wss
    #
    @41
    @48
    @9
    @50
    @0
    @2
    cC
    elpwi
    adantl
    ad2antrr
    @42
    @47
    @43
    simprl
    sseldd
    cC
    @28
    @14
    @13
    cX
    @38
    mrcsscl
    syl3anc
    @47
    @33
    @42
    @43
    @13
    @2
    elssuni
    ad2antrl
    sstrd
    rexlimddv
    anassrs
    adantrr
    adantlrr
    sstrd
    rexlimddv
    anassrs
    ralrimiva
    @0
    @5
    @12
    @19
    wa
    wb
    @9
    @3
    vx
    cC
    @4
    @14
    cX
    @38
    acsfiel
    ad2antrr
    mpbir2and
    ex
    ralrimiva
    jca
end
