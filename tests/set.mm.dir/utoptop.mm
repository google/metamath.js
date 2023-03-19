include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cutop.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "ctop.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "cpw.mm"
include "simpr.mm"
include "crab.mm"
include "utopval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "adantr.mm"
include "sstrd.mm"
include "sspwuni.mm"
include "sylib.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "sseldd.mm"
include "elutop.mm"
include "biimpa.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "syl21anc.mm"
include "r19.41v.mm"
include "ssuni.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl2anc.mm"
include "eluni2.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mpbir2and.mm"
include "ex.mm"
include "alrimiv.mm"
include "simpld.mm"
include "adantrr.mm"
include "ssinss1.mm"
include "syl.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr31.mm"
include "simpr32.mm"
include "ustincl.mm"
include "syl3anc.mm"
include "inss1.mm"
include "imass1.mm"
include "ax-mp.mm"
include "simpr33.mm"
include "syl5ss.mm"
include "inss2.mm"
include "ssind.mm"
include "wceq.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "3anassrs.mm"
include "simpll.mm"
include "simplrl.mm"
include "elin.mm"
include "simplrr.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "r19.29vva.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "fvex.mm"
include "istopg.mm"

theorem utoptop
  let cU: class U
  let cX: class X
  let va: setvar a
  let vp: setvar p
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- ( U e. ( UnifOn ` X ) -> ( unifTop ` U ) e. Top )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    vx
    cv
    #
    cU
    cutop
    cfv
    #
    wss
    #
    @1
    cuni
    #
    @2
    wcel
    #
    wi
    #
    vx
    wal
    #
    @1
    vy
    cv
    #
    cin
    #
    @2
    wcel
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @2
    ctop
    wcel
    #
    @0
    @6
    vx
    @0
    @3
    @5
    @0
    @3
    wa
    #
    @5
    @4
    cX
    wss
    #
    vv
    cv
    #
    vp
    cv
    #
    csn
    #
    cima
    #
    @4
    wss
    #
    vv
    cU
    wrex
    #
    vp
    @4
    wral
    #
    @13
    @1
    cX
    cpw
    #
    wss
    @14
    @13
    @1
    @2
    @22
    @0
    @3
    simpr
    @0
    @2
    @22
    wss
    @3
    @0
    @2
    @18
    va
    cv
    #
    wss
    vv
    cU
    wrex
    vp
    @23
    wral
    #
    va
    @22
    crab
    @22
    vp
    vv
    cU
    cX
    va
    utopval
    @24
    va
    @22
    ssrab2
    syl6eqss
    adantr
    sstrd
    @1
    cX
    sspwuni
    sylib
    @13
    @20
    vp
    @4
    @13
    @16
    @4
    wcel
    #
    wa
    #
    @16
    @8
    wcel
    #
    @20
    vy
    @1
    @26
    @8
    @1
    wcel
    #
    wa
    #
    @27
    wa
    #
    @18
    @8
    wss
    #
    vv
    cU
    wrex
    #
    @28
    @20
    @30
    @0
    @8
    @2
    wcel
    #
    @27
    @32
    @0
    @3
    @25
    @28
    @27
    simp-4l
    @30
    @1
    @2
    @8
    @0
    @3
    @25
    @28
    @27
    simp-4r
    @26
    @28
    @27
    simplr
    #
    sseldd
    @29
    @27
    simpr
    @0
    @33
    wa
    #
    @32
    vp
    @8
    @35
    @8
    cX
    wss
    #
    @32
    vp
    @8
    wral
    #
    @0
    @33
    @36
    @37
    wa
    vp
    vv
    @8
    cU
    cX
    elutop
    biimpa
    simprd
    r19.21bi
    #
    syl21anc
    @34
    @32
    @28
    wa
    @31
    @28
    wa
    #
    vv
    cU
    wrex
    @20
    @31
    @28
    vv
    cU
    r19.41v
    @39
    @19
    vv
    cU
    @18
    @8
    @1
    ssuni
    reximi
    sylbir
    syl2anc
    @25
    @27
    vy
    @1
    wrex
    #
    @13
    @25
    @40
    vy
    @16
    @1
    eluni2
    biimpi
    adantl
    r19.29a
    ralrimiva
    @0
    @5
    @14
    @21
    wa
    wb
    @3
    vp
    vv
    @4
    cU
    cX
    elutop
    adantr
    mpbir2and
    ex
    alrimiv
    @0
    @10
    vx
    vy
    @2
    @2
    @0
    @1
    @2
    wcel
    #
    @33
    wa
    #
    wa
    #
    @10
    @9
    cX
    wss
    #
    vw
    cv
    #
    @17
    cima
    #
    @9
    wss
    #
    vw
    cU
    wrex
    #
    vp
    @9
    wral
    #
    @43
    @1
    cX
    wss
    #
    @44
    @0
    @41
    @50
    @33
    @0
    @41
    wa
    #
    @50
    vu
    cv
    #
    @17
    cima
    #
    @1
    wss
    #
    vu
    cU
    wrex
    #
    vp
    @1
    wral
    #
    @0
    @41
    @50
    @56
    wa
    vp
    vu
    @1
    cU
    cX
    elutop
    biimpa
    #
    simpld
    adantrr
    @1
    @8
    cX
    ssinss1
    syl
    @43
    @48
    vp
    @9
    @43
    @16
    @9
    wcel
    #
    wa
    #
    @54
    @31
    wa
    #
    @48
    vu
    vv
    cU
    cU
    @59
    @52
    cU
    wcel
    #
    @15
    cU
    wcel
    #
    @60
    @48
    @0
    @42
    @58
    @61
    @62
    @60
    w3a
    #
    @48
    @0
    @42
    @58
    @63
    w3a
    #
    wa
    #
    @52
    @15
    cin
    #
    cU
    wcel
    #
    @66
    @17
    cima
    #
    @9
    wss
    #
    @48
    @65
    @0
    @61
    @62
    @67
    @0
    @64
    simpl
    @61
    @62
    @60
    @42
    @58
    @0
    simpr31
    @61
    @62
    @60
    @42
    @58
    @0
    simpr32
    cU
    @52
    @15
    cX
    ustincl
    syl3anc
    @65
    @68
    @1
    @8
    @65
    @68
    @53
    @1
    @66
    @52
    wss
    @68
    @53
    wss
    @52
    @15
    inss1
    @66
    @52
    @17
    imass1
    ax-mp
    @65
    @54
    @31
    @61
    @62
    @60
    @42
    @58
    @0
    simpr33
    #
    simpld
    syl5ss
    @65
    @68
    @18
    @8
    @66
    @15
    wss
    @68
    @18
    wss
    @52
    @15
    inss2
    @66
    @15
    @17
    imass1
    ax-mp
    @65
    @54
    @31
    @70
    simprd
    syl5ss
    ssind
    @47
    @69
    vw
    @66
    cU
    @45
    @66
    wceq
    @46
    @68
    @9
    @45
    @66
    @17
    imaeq1
    sseq1d
    rspcev
    syl2anc
    3anassrs
    3anassrs
    @59
    @55
    @32
    @60
    vv
    cU
    wrex
    vu
    cU
    wrex
    @59
    @0
    @41
    @16
    @1
    wcel
    #
    @55
    @0
    @42
    @58
    simpll
    #
    @0
    @41
    @33
    @58
    simplrl
    @59
    @71
    @27
    @59
    @58
    @71
    @27
    wa
    @43
    @58
    simpr
    @16
    @1
    @8
    elin
    sylib
    #
    simpld
    @51
    @55
    vp
    @1
    @51
    @50
    @56
    @57
    simprd
    r19.21bi
    syl21anc
    @59
    @0
    @33
    @27
    @32
    @72
    @0
    @41
    @33
    @58
    simplrr
    @59
    @71
    @27
    @73
    simprd
    @38
    syl21anc
    @54
    @31
    vu
    vv
    cU
    cU
    reeanv
    sylanbrc
    r19.29vva
    ralrimiva
    @0
    @10
    @44
    @49
    wa
    wb
    @42
    vp
    vw
    @9
    cU
    cX
    elutop
    adantr
    mpbir2and
    ralrimivva
    @2
    cvv
    wcel
    @12
    @7
    @11
    wa
    wb
    cU
    cutop
    fvex
    vx
    vy
    cvv
    @2
    istopg
    ax-mp
    sylanbrc
end
