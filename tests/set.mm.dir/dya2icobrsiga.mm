include "crn.mm"
include "cbrsiga.mm"
include "cv.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "ovex.mm"
include "elrnmpt2.mm"
include "wa.mm"
include "simpr.mm"
include "cmnf.mm"
include "cioo.mm"
include "cdif.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simpl.mm"
include "zred.mm"
include "crp.mm"
include "2rp.mm"
include "rpexpcld.mm"
include "rerpdivcld.mm"
include "rexrd.mm"
include "1red.mm"
include "readdcld.mm"
include "cr.mm"
include "mnflt.mm"
include "syl.mm"
include "difioo.mm"
include "syl31anc.mm"
include "csiga.mm"
include "cuni.mm"
include "cfv.mm"
include "brsigarn.mm"
include "elrnsiga.mm"
include "ax-mp.mm"
include "ctg.mm"
include "csigagen.mm"
include "ctop.mm"
include "retop.mm"
include "iooretop.mm"
include "elsigagen.mm"
include "mp2an.mm"
include "df-brsiga.mm"
include "eleqtrri.mm"
include "difelsiga.mm"
include "mp3an.mm"
include "syl6eqelr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem dya2icobrsiga
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let vd: setvar d
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )

  disjoint n x
  disjoint n x
  disjoint d n
  disjoint d x
  disjoint I d
  assert |- ran I C_ BrSiga

  proof
    vd
    cI
    crn
    #
    cbrsiga
    vd
    cv
    #
    @0
    wcel
    @1
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
    @2
    c1
    caddc
    co
    #
    @4
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
    @1
    cbrsiga
    wcel
    #
    vx
    vn
    cz
    cz
    @8
    @1
    cI
    dya2ioc.1
    @5
    @7
    cico
    ovex
    elrnmpt2
    @9
    @10
    vx
    vn
    cz
    cz
    @2
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    wa
    #
    @9
    @10
    @13
    @9
    wa
    @1
    @8
    cbrsiga
    @13
    @9
    simpr
    @13
    @8
    cbrsiga
    wcel
    @9
    @13
    @8
    cmnf
    @7
    cioo
    co
    #
    cmnf
    @5
    cioo
    co
    #
    cdif
    #
    cbrsiga
    @13
    cmnf
    cxr
    wcel
    #
    @5
    cxr
    wcel
    @7
    cxr
    wcel
    cmnf
    @5
    clt
    wbr
    #
    @16
    @8
    wceq
    @17
    @13
    mnfxr
    a1i
    @13
    @5
    @13
    @2
    @4
    @13
    @2
    @11
    @12
    simpl
    zred
    #
    @13
    c2
    @3
    c2
    crp
    wcel
    @13
    2rp
    a1i
    @11
    @12
    simpr
    rpexpcld
    #
    rerpdivcld
    #
    rexrd
    @13
    @7
    @13
    @6
    @4
    @13
    @2
    c1
    @19
    @13
    1red
    readdcld
    @20
    rerpdivcld
    rexrd
    @13
    @5
    cr
    wcel
    @18
    @21
    @5
    mnflt
    syl
    cmnf
    @5
    @7
    difioo
    syl31anc
    cbrsiga
    csiga
    crn
    cuni
    wcel
    #
    @14
    cbrsiga
    wcel
    @15
    cbrsiga
    wcel
    @16
    cbrsiga
    wcel
    cbrsiga
    cr
    csiga
    cfv
    wcel
    @22
    brsigarn
    cbrsiga
    cr
    elrnsiga
    ax-mp
    @14
    cioo
    crn
    ctg
    cfv
    #
    csigagen
    cfv
    #
    cbrsiga
    @23
    ctop
    wcel
    #
    @14
    @23
    wcel
    @14
    @24
    wcel
    retop
    cmnf
    @7
    iooretop
    @23
    @14
    ctop
    elsigagen
    mp2an
    df-brsiga
    eleqtrri
    @15
    @24
    cbrsiga
    @25
    @15
    @23
    wcel
    @15
    @24
    wcel
    retop
    cmnf
    @5
    iooretop
    @23
    @15
    ctop
    elsigagen
    mp2an
    df-brsiga
    eleqtrri
    @14
    @15
    cbrsiga
    difelsiga
    mp3an
    syl6eqelr
    adantr
    eqeltrd
    ex
    rexlimivv
    sylbi
    ssriv
end
