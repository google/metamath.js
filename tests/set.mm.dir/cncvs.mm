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
include "cnrlmod.mm"
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
include "crglmod.mm"
include "csca.mm"
include "rlmsca.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "isclmi.mm"
include "mp3an.mm"
include "cnrlvec.mm"
include "elin.mm"
include "mpbir2an.mm"
include "df-cvs.mm"
include "eleqtrri.mm"

theorem cncvs
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume cnrlmod.c: |- C = ( ringLMod ` CCfld )


  assert |- C e. CVec

  proof
    cC
    cclm
    clvec
    cin
    #
    ccvs
    cC
    @0
    wcel
    cC
    cclm
    wcel
    #
    cC
    clvec
    wcel
    cC
    clmod
    wcel
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
    cC
    cnrlmod.c
    cnrlmod
    @2
    ccnfld
    ccnfld
    cvv
    wcel
    #
    @2
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
    @4
    vy
    cv
    #
    addcl
    @4
    negcl
    ax-1cn
    @4
    @5
    mulcl
    cnsubrglem
    ccnfld
    cc
    cC
    ccnfld
    ccnfld
    crglmod
    cfv
    #
    csca
    cfv
    #
    cC
    csca
    cfv
    @3
    ccnfld
    @7
    wceq
    cnfldex
    ccnfld
    cvv
    rlmsca
    ax-mp
    @6
    cC
    csca
    cC
    @6
    cnrlmod.c
    eqcomi
    fveq2i
    eqtri
    isclmi
    mp3an
    cC
    cnrlmod.c
    cnrlvec
    cC
    cclm
    clvec
    elin
    mpbir2an
    df-cvs
    eleqtrri
end
