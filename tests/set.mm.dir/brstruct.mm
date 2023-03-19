include "cv.mm"
include "cle.mm"
include "cn.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cstr.mm"
include "df-struct.mm"
include "relopabi.mm"

theorem brstruct
  let vf: setvar f
  let vx: setvar x


  assert |- Rel Struct

  proof
    vx
    cv
    #
    cle
    cn
    cn
    cxp
    cin
    wcel
    vf
    cv
    #
    c0
    csn
    cdif
    wfun
    @1
    cdm
    @0
    cfz
    cfv
    wss
    w3a
    vf
    vx
    cstr
    vx
    vf
    df-struct
    relopabi
end
