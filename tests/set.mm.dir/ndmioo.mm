include "cxr.mm"
include "cioo.mm"
include "cxp.mm"
include "cpw.mm"
include "clt.mm"
include "df-ioo.mm"
include "ixxf.mm"
include "fdmi.mm"
include "ndmov.mm"

theorem ndmioo
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( -. ( A e. RR* /\ B e. RR* ) -> ( A (,) B ) = (/) )

  proof
    cA
    cB
    cxr
    cioo
    cxr
    cxr
    cxp
    cxr
    cpw
    cioo
    vx
    vy
    vz
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    ixxf
    fdmi
    ndmov
end
