include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cxp.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cuni.mm"
include "ctx.mm"
include "ccld.mm"
include "cfv.mm"
include "wceq.mm"
include "csigagen.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "sxbrsigalem0.mm"
include "cioo.mm"
include "ctg.mm"
include "ctop.mm"
include "retop.mm"
include "eqeltri.mm"
include "txtopi.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "txunii.mm"
include "unicls.mm"
include "wfn.mm"
include "wral.mm"
include "ovex.mm"
include "reex.mm"
include "xpex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "weq.mm"
include "oveq1.mm"
include "xpeq1d.mm"
include "fvmpt.mm"
include "icopnfcld.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "c0.mm"
include "cdif.mm"
include "dif0.mm"
include "0opn.mm"
include "ax-mp.mm"
include "opncld.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "txcld.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "fnfvrnss.mm"
include "xpeq2d.mm"
include "sylancr.mm"
include "unssi.mm"
include "fvex.mm"
include "sssigagen.mm"
include "sstri.mm"
include "sigagenss2.mm"
include "mp3an.mm"

theorem sxbrsigalem3
  let ve: setvar e
  let vf: setvar f
  let cJ: class J
  let vu: setvar u
  let vv: setvar v
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )

  disjoint e f
  disjoint e u
  disjoint e v
  disjoint f u
  disjoint f v
  disjoint u v
  disjoint J u
  disjoint J v
  assert |- ( sigaGen ` ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) ) u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) ) C_ ( sigaGen ` ( Clsd ` ( J tX J ) ) )

  proof
    ve
    cr
    ve
    cv
    #
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    cmpt
    #
    crn
    #
    vf
    cr
    cr
    vf
    cv
    #
    cpnf
    cico
    co
    #
    cxp
    #
    cmpt
    #
    crn
    #
    cun
    #
    cuni
    #
    cJ
    cJ
    ctx
    co
    #
    ccld
    cfv
    #
    cuni
    #
    wceq
    @10
    @13
    csigagen
    cfv
    #
    wss
    @13
    cvv
    wcel
    #
    @10
    csigagen
    cfv
    @15
    wss
    @11
    cr
    cr
    cxp
    #
    @14
    ve
    vf
    sxbrsigalem0
    @12
    @17
    cJ
    cJ
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    sxbrsiga.0
    retop
    eqeltri
    #
    @19
    txtopi
    cJ
    cJ
    cr
    cr
    @19
    @19
    cr
    @18
    cuni
    cJ
    cuni
    uniretop
    cJ
    @18
    sxbrsiga.0
    unieqi
    eqtr4i
    #
    @20
    txunii
    unicls
    eqtr4i
    @10
    @13
    @15
    @4
    @9
    @13
    @3
    cr
    wfn
    vu
    cv
    #
    @3
    cfv
    #
    @13
    wcel
    #
    vu
    cr
    wral
    @4
    @13
    wss
    ve
    cr
    @2
    @3
    @1
    cr
    @0
    cpnf
    cico
    ovex
    reex
    xpex
    @3
    eqid
    #
    fnmpti
    @23
    vu
    cr
    @21
    cr
    wcel
    #
    @22
    @21
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    @13
    ve
    @21
    @2
    @27
    cr
    @3
    ve
    vu
    weq
    @1
    @26
    cr
    @0
    @21
    cpnf
    cico
    oveq1
    xpeq1d
    @24
    @26
    cr
    @21
    cpnf
    cico
    ovex
    reex
    xpex
    fvmpt
    @25
    @26
    cJ
    ccld
    cfv
    #
    wcel
    cr
    @28
    wcel
    #
    @27
    @13
    wcel
    @25
    @26
    @18
    ccld
    cfv
    #
    @28
    @21
    icopnfcld
    cJ
    @18
    ccld
    sxbrsiga.0
    fveq2i
    #
    syl6eleqr
    cr
    c0
    cdif
    #
    cr
    @28
    cr
    dif0
    cJ
    ctop
    wcel
    #
    c0
    cJ
    wcel
    #
    @32
    @28
    wcel
    @19
    @33
    @34
    @19
    cJ
    0opn
    ax-mp
    c0
    cJ
    cr
    @20
    opncld
    mp2an
    eqeltrri
    #
    @26
    cr
    cJ
    cJ
    txcld
    sylancl
    eqeltrd
    rgen
    vu
    cr
    @13
    @3
    fnfvrnss
    mp2an
    @8
    cr
    wfn
    vv
    cv
    #
    @8
    cfv
    #
    @13
    wcel
    #
    vv
    cr
    wral
    @9
    @13
    wss
    vf
    cr
    @7
    @8
    cr
    @6
    reex
    @5
    cpnf
    cico
    ovex
    xpex
    @8
    eqid
    #
    fnmpti
    @38
    vv
    cr
    @36
    cr
    wcel
    #
    @37
    cr
    @36
    cpnf
    cico
    co
    #
    cxp
    #
    @13
    vf
    @36
    @7
    @42
    cr
    @8
    vf
    vv
    weq
    @6
    @41
    cr
    @5
    @36
    cpnf
    cico
    oveq1
    xpeq2d
    @39
    cr
    @41
    reex
    @36
    cpnf
    cico
    ovex
    xpex
    fvmpt
    @40
    @29
    @41
    @28
    wcel
    @42
    @13
    wcel
    @35
    @40
    @41
    @30
    @28
    @36
    icopnfcld
    @31
    syl6eleqr
    cr
    @41
    cJ
    cJ
    txcld
    sylancr
    eqeltrd
    rgen
    vv
    cr
    @13
    @8
    fnfvrnss
    mp2an
    unssi
    @16
    @13
    @15
    wss
    @12
    ccld
    fvex
    #
    @13
    cvv
    sssigagen
    ax-mp
    sstri
    @43
    @10
    @13
    cvv
    sigagenss2
    mp3an
end
