include "cado.mm"
include "ccnv.mm"
include "wfun.mm"
include "funadj.mm"
include "cnvadj.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem funcnvadj
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- Fun `' adjh

  proof
    cado
    ccnv
    #
    wfun
    cado
    wfun
    funadj
    @0
    cado
    cnvadj
    funeqi
    mpbir
end
