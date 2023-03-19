include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "dnif.mm"
include "wa.mm"
include "simpr.mm"
include "simplr.mm"
include "dnicld2.mm"
include "simplll.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "ad2antrr.mm"
include "rpred.mm"
include "dnibnd.mm"
include "lelttrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rgen2.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "ax-resscn.mm"
include "elcncf2.mm"
include "mp2an.mm"
include "mpbir2an.mm"

theorem dnicn
  let vx: setvar x
  let cT: class T
  let vd: setvar d
  let ve: setvar e
  let vy: setvar y
  let vz: setvar z
  assume dnicn.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )


  assert |- T e. ( RR -cn-> RR )

  proof
    cT
    cr
    cr
    ccncf
    co
    wcel
    #
    cr
    cr
    cT
    wf
    #
    vz
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    clt
    wbr
    #
    @2
    cT
    cfv
    #
    @3
    cT
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cr
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    vy
    cr
    wral
    #
    vx
    cT
    dnicn.1
    dnif
    @16
    vy
    ve
    cr
    crp
    @3
    cr
    wcel
    #
    @12
    crp
    wcel
    #
    wa
    #
    @19
    @5
    @12
    clt
    wbr
    #
    @13
    wi
    #
    vz
    cr
    wral
    #
    @16
    @18
    @19
    simpr
    #
    @20
    @22
    vz
    cr
    @20
    @2
    cr
    wcel
    #
    wa
    #
    @21
    @13
    @26
    @21
    wa
    #
    @11
    @5
    @12
    @27
    @10
    @27
    @10
    @27
    @8
    @9
    @27
    vx
    @2
    cT
    dnicn.1
    @20
    @25
    @21
    simplr
    #
    dnicld2
    @27
    vx
    @3
    cT
    dnicn.1
    @18
    @19
    @25
    @21
    simplll
    #
    dnicld2
    resubcld
    recnd
    abscld
    @27
    @4
    @27
    @4
    @27
    @2
    @3
    @28
    @29
    resubcld
    recnd
    abscld
    @27
    @12
    @20
    @19
    @25
    @21
    @24
    ad2antrr
    rpred
    @27
    vx
    @3
    @2
    cT
    dnicn.1
    @29
    @28
    dnibnd
    @26
    @21
    simpr
    lelttrd
    ex
    ralrimiva
    @15
    @23
    vd
    @12
    crp
    @6
    @12
    wceq
    #
    @14
    @22
    vz
    cr
    @30
    @7
    @21
    @13
    @6
    @12
    @5
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rgen2
    cr
    cc
    wss
    #
    @31
    @0
    @1
    @17
    wa
    wb
    ax-resscn
    ax-resscn
    vy
    ve
    vd
    vz
    cr
    cr
    cT
    elcncf2
    mp2an
    mpbir2an
end
