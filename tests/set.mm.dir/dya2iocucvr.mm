include "crn.mm"
include "cuni.mm"
include "cr.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "unissb.mm"
include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "vex.mm"
include "xpex.mm"
include "elrnmpt2.mm"
include "wa.mm"
include "simpr.mm"
include "cpw.mm"
include "pwssb.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "cz.mm"
include "ovex.mm"
include "cxr.mm"
include "simpll.mm"
include "zred.mm"
include "2re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "simplr.mm"
include "reexpclzd.mm"
include "2cnd.mm"
include "expne0d.mm"
include "redivcld.mm"
include "1red.mm"
include "readdcld.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "eqsstrd.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "sseli.mm"
include "elpwid.mm"
include "xpss12.mm"
include "syl2an.mm"
include "adantr.mm"
include "ctx.mm"
include "ctop.mm"
include "cioo.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "txtopi.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "txunii.mm"
include "topopn.mm"
include "dya2iocuni.mm"
include "mp2b.mm"
include "elpwi.mm"
include "unissd.mm"
include "eqsstr3d.mm"
include "rexlimiva.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem dya2iocucvr
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint n u
  disjoint n v
  disjoint n x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint I u
  disjoint I v
  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint c d
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint I d
  disjoint R c
  disjoint R d
  assert |- U. ran R = ( RR X. RR )

  proof
    cR
    crn
    #
    cuni
    #
    cr
    cr
    cxp
    #
    @1
    @2
    wss
    vd
    cv
    #
    @2
    wss
    #
    vd
    @0
    vd
    @0
    @2
    unissb
    @3
    @0
    wcel
    @3
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    wceq
    #
    vv
    cI
    crn
    #
    wrex
    vu
    @9
    wrex
    @4
    vu
    vv
    @9
    @9
    @7
    @3
    cR
    dya2ioc.2
    @5
    @6
    vu
    vex
    vv
    vex
    xpex
    elrnmpt2
    @8
    @4
    vu
    vv
    @9
    @9
    @5
    @9
    wcel
    #
    @6
    @9
    wcel
    #
    wa
    #
    @8
    @4
    @12
    @8
    wa
    @3
    @7
    @2
    @12
    @8
    simpr
    @12
    @7
    @2
    wss
    #
    @8
    @10
    @5
    cr
    wss
    @6
    cr
    wss
    @13
    @11
    @10
    @5
    cr
    @9
    cr
    cpw
    #
    @5
    @9
    @14
    wss
    @3
    cr
    wss
    #
    vd
    @9
    vd
    @9
    cr
    pwssb
    @3
    @9
    wcel
    @3
    vx
    cv
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @16
    c1
    caddc
    co
    #
    @18
    cdiv
    co
    #
    cico
    co
    #
    wceq
    #
    vn
    cz
    wrex
    vx
    cz
    wrex
    @15
    vx
    vn
    cz
    cz
    @22
    @3
    cI
    dya2ioc.1
    @19
    @21
    cico
    ovex
    elrnmpt2
    @23
    @15
    vx
    vn
    cz
    cz
    @16
    cz
    wcel
    #
    @17
    cz
    wcel
    #
    wa
    #
    @23
    @15
    @26
    @23
    wa
    #
    @3
    @22
    cr
    @26
    @23
    simpr
    @27
    @19
    cr
    wcel
    @21
    cxr
    wcel
    @22
    cr
    wss
    @27
    @16
    @18
    @27
    @16
    @24
    @25
    @23
    simpll
    zred
    #
    @27
    c2
    @17
    c2
    cr
    wcel
    @27
    2re
    a1i
    c2
    cc0
    wne
    @27
    2ne0
    a1i
    #
    @24
    @25
    @23
    simplr
    #
    reexpclzd
    #
    @27
    c2
    @17
    @27
    2cnd
    @29
    @30
    expne0d
    #
    redivcld
    @27
    @21
    @27
    @20
    @18
    @27
    @16
    c1
    @28
    @27
    1red
    readdcld
    @31
    @32
    redivcld
    rexrd
    @19
    @21
    icossre
    syl2anc
    eqsstrd
    ex
    rexlimivv
    sylbi
    mprgbir
    #
    sseli
    elpwid
    @11
    @6
    cr
    @9
    @14
    @6
    @33
    sseli
    elpwid
    @5
    cr
    @6
    cr
    xpss12
    syl2an
    adantr
    eqsstrd
    ex
    rexlimivv
    sylbi
    mprgbir
    vc
    cv
    #
    cuni
    #
    @2
    wceq
    #
    vc
    @0
    cpw
    #
    wrex
    #
    @2
    @1
    wss
    #
    cJ
    cJ
    ctx
    co
    #
    ctop
    wcel
    @2
    @40
    wcel
    @38
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
    @42
    txtopi
    @40
    @2
    cJ
    cJ
    cr
    cr
    @42
    @42
    cr
    @41
    cuni
    cJ
    cuni
    uniretop
    cJ
    @41
    sxbrsiga.0
    unieqi
    eqtr4i
    #
    @43
    txunii
    topopn
    vx
    vv
    vu
    @2
    cR
    vn
    cI
    cJ
    vc
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocuni
    mp2b
    @36
    @39
    vc
    @37
    @34
    @37
    wcel
    #
    @36
    wa
    #
    @2
    @35
    @1
    @44
    @36
    simpr
    @45
    @34
    @0
    @44
    @34
    @0
    wss
    @36
    @34
    @0
    elpwi
    adantr
    unissd
    eqsstr3d
    rexlimiva
    ax-mp
    eqssi
end
