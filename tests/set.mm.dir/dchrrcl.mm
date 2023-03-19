include "wcel.mm"
include "cdchr.mm"
include "cdm.mm"
include "cn.mm"
include "cv.mm"
include "czn.mm"
include "cfv.mm"
include "cbs.mm"
include "cui.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "crab.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cmul.mm"
include "cof.mm"
include "cres.mm"
include "cpr.mm"
include "csb.mm"
include "df-dchr.mm"
include "dmmptss.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "syl.mm"
include "nsyl2.mm"
include "sseldi.mm"

theorem dchrrcl
  let cD: class D
  let cG: class G
  let cN: class N
  let cX: class X
  let vb: setvar b
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  assume dchrrcl.g: |- G = ( DChr ` N )
  assume dchrrcl.b: |- D = ( Base ` G )


  assert |- ( X e. D -> N e. NN )

  proof
    cX
    cD
    wcel
    #
    cdchr
    cdm
    #
    cn
    cN
    vn
    cn
    vz
    vn
    cv
    czn
    cfv
    vb
    vz
    cv
    #
    cbs
    cfv
    @2
    cui
    cfv
    cdif
    cc0
    csn
    cxp
    vx
    cv
    wss
    vx
    @2
    cmgp
    cfv
    ccnfld
    cmgp
    cfv
    cmhm
    co
    crab
    cnx
    cbs
    cfv
    vb
    cv
    #
    cop
    cnx
    cplusg
    cfv
    cmul
    cof
    @3
    @3
    cxp
    cres
    cop
    cpr
    csb
    csb
    cdchr
    vx
    vz
    vn
    vb
    df-dchr
    dmmptss
    @0
    cD
    c0
    wceq
    #
    cN
    @1
    wcel
    #
    cD
    cX
    n0i
    @5
    wn
    #
    cG
    c0
    wceq
    #
    @4
    @6
    cG
    cN
    cdchr
    cfv
    c0
    dchrrcl.g
    cN
    cdchr
    ndmfv
    syl5eq
    @7
    cG
    cbs
    cfv
    c0
    cbs
    cfv
    cD
    c0
    cG
    c0
    cbs
    fveq2
    dchrrcl.b
    base0
    3eqtr4g
    syl
    nsyl2
    sseldi
end
