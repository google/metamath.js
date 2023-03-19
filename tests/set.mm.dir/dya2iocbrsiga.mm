include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "cbrsiga.mm"
include "dya2iocival.mm"
include "cmnf.mm"
include "cioo.mm"
include "cdif.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simpr.mm"
include "zred.mm"
include "crp.mm"
include "2rp.mm"
include "simpl.mm"
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
include "crn.mm"
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
include "eqeltrd.mm"

theorem dya2iocbrsiga
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )

  disjoint n x
  assert |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) e. BrSiga )

  proof
    cN
    cz
    wcel
    #
    cX
    cz
    wcel
    #
    wa
    #
    cX
    cN
    cI
    co
    cX
    c2
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cX
    c1
    caddc
    co
    #
    @3
    cdiv
    co
    #
    cico
    co
    #
    cbrsiga
    vx
    vn
    cI
    cJ
    cN
    cX
    sxbrsiga.0
    dya2ioc.1
    dya2iocival
    @2
    @7
    cmnf
    @6
    cioo
    co
    #
    cmnf
    @4
    cioo
    co
    #
    cdif
    #
    cbrsiga
    @2
    cmnf
    cxr
    wcel
    #
    @4
    cxr
    wcel
    @6
    cxr
    wcel
    cmnf
    @4
    clt
    wbr
    #
    @10
    @7
    wceq
    @11
    @2
    mnfxr
    a1i
    @2
    @4
    @2
    cX
    @3
    @2
    cX
    @0
    @1
    simpr
    zred
    #
    @2
    c2
    cN
    c2
    crp
    wcel
    @2
    2rp
    a1i
    @0
    @1
    simpl
    rpexpcld
    #
    rerpdivcld
    #
    rexrd
    @2
    @6
    @2
    @5
    @3
    @2
    cX
    c1
    @13
    @2
    1red
    readdcld
    @14
    rerpdivcld
    rexrd
    @2
    @4
    cr
    wcel
    @12
    @15
    @4
    mnflt
    syl
    cmnf
    @4
    @6
    difioo
    syl31anc
    cbrsiga
    csiga
    crn
    cuni
    wcel
    #
    @8
    cbrsiga
    wcel
    @9
    cbrsiga
    wcel
    @10
    cbrsiga
    wcel
    cbrsiga
    cr
    csiga
    cfv
    wcel
    @16
    brsigarn
    cbrsiga
    cr
    elrnsiga
    ax-mp
    @8
    cioo
    crn
    ctg
    cfv
    #
    csigagen
    cfv
    #
    cbrsiga
    @17
    ctop
    wcel
    #
    @8
    @17
    wcel
    @8
    @18
    wcel
    retop
    cmnf
    @6
    iooretop
    @17
    @8
    ctop
    elsigagen
    mp2an
    df-brsiga
    eleqtrri
    @9
    @18
    cbrsiga
    @19
    @9
    @17
    wcel
    @9
    @18
    wcel
    retop
    cmnf
    @4
    iooretop
    @17
    @9
    ctop
    elsigagen
    mp2an
    df-brsiga
    eleqtrri
    @8
    @9
    cbrsiga
    difelsiga
    mp3an
    syl6eqelr
    eqeltrd
end
