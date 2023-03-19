include "cclm.mm"
include "clvec.mm"
include "cin.mm"
include "ccvs.mm"
include "wcel.mm"
include "clmod.mm"
include "ccnfld.mm"
include "cc.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cfv.mm"
include "cnlmod.mm"
include "cvv.mm"
include "cnfldex.mm"
include "cnfldbas.mm"
include "ressid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cv.mm"
include "id.mm"
include "addcl.mm"
include "negcl.mm"
include "ax-1cn.mm"
include "mulcl.mm"
include "cnsubrglem.mm"
include "csca.mm"
include "caddc.mm"
include "cmul.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "cvsca.mm"
include "cun.mm"
include "ctp.mm"
include "csn.mm"
include "qdass.mm"
include "eqtri.mm"
include "lmodsca.mm"
include "isclmi.mm"
include "mp3an.mm"
include "cdr.mm"
include "cndrng.mm"
include "islvec.mm"
include "mpbir2an.mm"
include "elin.mm"
include "df-cvs.mm"
include "eleqtrri.mm"

theorem cnstrcvs
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnlmod.w: |- W = ( { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. } u. { <. ( Scalar ` ndx ) , CCfld >. , <. ( .s ` ndx ) , x. >. } )


  assert |- W e. CVec

  proof
    cW
    cclm
    clvec
    cin
    #
    ccvs
    cW
    @0
    wcel
    cW
    cclm
    wcel
    #
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    ccnfld
    ccnfld
    cc
    cress
    co
    #
    wceq
    cc
    ccnfld
    csubrg
    cfv
    wcel
    @1
    cW
    cnlmod.w
    cnlmod
    #
    @4
    ccnfld
    ccnfld
    cvv
    wcel
    #
    @4
    ccnfld
    wceq
    cnfldex
    cc
    ccnfld
    cvv
    cnfldbas
    ressid
    ax-mp
    eqcomi
    vx
    vy
    cc
    vx
    cv
    #
    cc
    wcel
    id
    @7
    vy
    cv
    #
    addcl
    @7
    negcl
    ax-1cn
    @7
    @8
    mulcl
    cnsubrglem
    ccnfld
    cc
    cW
    @6
    ccnfld
    cW
    csca
    cfv
    wceq
    cnfldex
    cc
    caddc
    cmul
    ccnfld
    cW
    cvv
    cW
    cnx
    cbs
    cfv
    cc
    cop
    #
    cnx
    cplusg
    cfv
    caddc
    cop
    #
    cpr
    cnx
    csca
    cfv
    ccnfld
    cop
    #
    cnx
    cvsca
    cfv
    cmul
    cop
    #
    cpr
    cun
    @9
    @10
    @11
    ctp
    @12
    csn
    cun
    cnlmod.w
    @9
    @10
    @11
    @12
    qdass
    eqtri
    lmodsca
    ax-mp
    #
    isclmi
    mp3an
    @2
    @3
    ccnfld
    cdr
    wcel
    @5
    cndrng
    ccnfld
    cW
    @13
    islvec
    mpbir2an
    cW
    cclm
    clvec
    elin
    mpbir2an
    df-cvs
    eleqtrri
end
