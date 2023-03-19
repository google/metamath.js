include "cxr.mm"
include "cxp.mm"
include "cpw.mm"
include "cico.mm"
include "cle.mm"
include "clt.mm"
include "df-ico.mm"
include "ixxf.mm"
include "fdmi.mm"

theorem dmico
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- dom [,) = ( RR* X. RR* )

  proof
    cxr
    cxr
    cxp
    cxr
    cpw
    cico
    vx
    vy
    vz
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
    ixxf
    fdmi
end
