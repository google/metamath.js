include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wne.mm"
include "cr.mm"
include "crp.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "logdmn0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssriv.mm"

theorem logdmss
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- D C_ ( CC \ { 0 } )

  proof
    vx
    cD
    cc
    cc0
    csn
    cdif
    #
    vx
    cv
    #
    cD
    wcel
    #
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    @1
    @0
    wcel
    @2
    @3
    @1
    cr
    wcel
    @1
    crp
    wcel
    wi
    @1
    cD
    logcn.d
    ellogdm
    simplbi
    @1
    cD
    logcn.d
    logdmn0
    @1
    cc
    cc0
    eldifsn
    sylanbrc
    ssriv
end
