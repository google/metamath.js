include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cop.mm"
include "ccnfld.mm"
include "wcel.mm"
include "ccusgr.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "cstv.mm"
include "ccj.mm"
include "csn.mm"
include "cun.mm"
include "cts.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "cunif.mm"
include "cmetu.mm"
include "wo.mm"
include "opex.mm"
include "tpid1.mm"
include "orci.mm"
include "elun.mm"
include "mpbir.mm"
include "df-cnfld.mm"
include "eleq2i.mm"
include "bitri.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cnfldbas.mm"
include "pweqi.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "cstr.mm"
include "wbr.mm"
include "cnfldstr.mm"
include "a1i.mm"
include "fvex.mm"
include "cnex.mm"
include "opeldm.mm"
include "structtocusgr.mm"

theorem cffldtocusgr
  let vx: setvar x
  let cP: class P
  let cG: class G
  assume cffldtocusgr.p: |- P = { x e. ~P CC | ( # ` x ) = 2 }
  assume cffldtocusgr.g: |- G = ( CCfld sSet <. ( .ef ` ndx ) , ( _I |` P ) >. )

  disjoint G x
  disjoint P x
  assert |- G e. ComplUSGraph

  proof
    cnx
    cbs
    cfv
    #
    cc
    cop
    #
    ccnfld
    wcel
    #
    cG
    ccusgr
    wcel
    @2
    @1
    @1
    cnx
    cplusg
    cfv
    caddc
    cop
    #
    cnx
    cmulr
    cfv
    cmul
    cop
    #
    ctp
    #
    cnx
    cstv
    cfv
    ccj
    cop
    csn
    #
    cun
    #
    wcel
    #
    @1
    cnx
    cts
    cfv
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    cop
    cnx
    cple
    cfv
    cle
    cop
    cnx
    cds
    cfv
    @9
    cop
    ctp
    cnx
    cunif
    cfv
    @9
    cmetu
    cfv
    cop
    csn
    cun
    #
    wcel
    #
    wo
    #
    @8
    @11
    @8
    @1
    @5
    wcel
    #
    @1
    @6
    wcel
    #
    wo
    @13
    @14
    @1
    @3
    @4
    @0
    cc
    opex
    tpid1
    orci
    @1
    @5
    @6
    elun
    mpbir
    orci
    @2
    @1
    @7
    @10
    cun
    #
    wcel
    @12
    ccnfld
    @15
    @1
    df-cnfld
    eleq2i
    @1
    @7
    @10
    elun
    bitri
    mpbir
    @2
    vx
    cP
    ccnfld
    cG
    c1
    c1
    c3
    cdc
    cop
    #
    cP
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cc
    cpw
    #
    crab
    #
    @17
    vx
    ccnfld
    cbs
    cfv
    #
    cpw
    #
    crab
    #
    cffldtocusgr.p
    @18
    @21
    wceq
    @19
    @22
    wceq
    cc
    @20
    cnfldbas
    pweqi
    @17
    vx
    @18
    @21
    rabeq
    ax-mp
    eqtri
    ccnfld
    @16
    cstr
    wbr
    @2
    cnfldstr
    a1i
    cffldtocusgr.g
    @0
    cc
    ccnfld
    cnx
    cbs
    fvex
    cnex
    opeldm
    structtocusgr
    ax-mp
end
