include "chli.mm"
include "cdm.mm"
include "chil.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wfun.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cims.mm"
include "cmopn.mm"
include "clm.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cxmt.mm"
include "cha.mm"
include "eqid.mm"
include "hhxmet.mm"
include "methaus.mm"
include "lmfun.mm"
include "mp2b.mm"
include "funres.mm"
include "ax-mp.mm"
include "hhlm.mm"
include "funeqi.mm"
include "mpbir.mm"
include "funfn.mm"
include "mpbi.mm"
include "wbr.mm"
include "wb.mm"
include "funfvbrb.mm"
include "fvex.mm"
include "hlimveci.mm"
include "sylbi.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem hlimf
  let vx: setvar x


  assert |- ~~>v : dom ~~>v --> ~H

  proof
    chli
    cdm
    #
    chil
    chli
    wf
    chli
    @0
    wfn
    #
    vx
    cv
    #
    chli
    cfv
    #
    chil
    wcel
    #
    vx
    @0
    wral
    chli
    wfun
    #
    @1
    @5
    cva
    csm
    cop
    cno
    cop
    #
    cims
    cfv
    #
    cmopn
    cfv
    #
    clm
    cfv
    #
    chil
    cn
    cmap
    co
    #
    cres
    #
    wfun
    #
    @9
    wfun
    #
    @12
    @7
    chil
    cxmt
    cfv
    wcel
    @8
    cha
    wcel
    @13
    @7
    @6
    @6
    eqid
    #
    @7
    eqid
    #
    hhxmet
    @7
    @8
    chil
    @8
    eqid
    #
    methaus
    @8
    lmfun
    mp2b
    @10
    @9
    funres
    ax-mp
    chli
    @11
    @7
    @6
    @8
    @14
    @15
    @16
    hhlm
    funeqi
    mpbir
    #
    chli
    funfn
    mpbi
    @4
    vx
    @0
    @2
    @0
    wcel
    #
    @2
    @3
    chli
    wbr
    #
    @4
    @5
    @18
    @19
    wb
    @17
    @2
    chli
    funfvbrb
    ax-mp
    @3
    @2
    @2
    chli
    fvex
    hlimveci
    sylbi
    rgen
    vx
    @0
    chil
    chli
    ffnfv
    mpbir2an
end
