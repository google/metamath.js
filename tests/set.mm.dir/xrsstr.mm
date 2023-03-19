include "cxr.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cxmu.mm"
include "cordt.mm"
include "cfv.mm"
include "cxrs.mm"
include "df-xrs.mm"
include "odrngstr.mm"

theorem xrsstr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- RR*s Struct <. 1 , ; 1 2 >.

  proof
    cxr
    vx
    vy
    cxr
    cxr
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    @1
    @0
    cxne
    cxad
    co
    @0
    @1
    cxne
    cxad
    co
    cif
    cmpt2
    cxad
    cxmu
    cle
    cordt
    cfv
    cle
    cxrs
    vx
    vy
    df-xrs
    odrngstr
end
