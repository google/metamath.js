include "cn.mm"
include "ccnfld.mm"
include "cpl1.mm"
include "cfv.mm"
include "cmgp.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "cod.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cv1.mm"
include "cascl.mm"
include "csg.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ccytp.mm"
include "ovex.mm"
include "df-cytp.mm"
include "fnmpti.mm"

theorem cytpfn
  let vn: setvar n
  let vr: setvar r


  assert |- CytP Fn NN

  proof
    vn
    cn
    ccnfld
    cpl1
    cfv
    #
    cmgp
    cfv
    #
    vr
    ccnfld
    cmgp
    cfv
    cc
    cc0
    csn
    cdif
    cress
    co
    cod
    cfv
    ccnv
    vn
    cv
    csn
    cima
    ccnfld
    cv1
    cfv
    vr
    cv
    @0
    cascl
    cfv
    cfv
    @0
    csg
    cfv
    co
    cmpt
    #
    cgsu
    co
    ccytp
    @1
    @2
    cgsu
    ovex
    vn
    vr
    df-cytp
    fnmpti
end
