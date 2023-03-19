include "culm.mm"
include "cfv.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "wb.mm"
include "wrel.mm"
include "cv.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ulmrel.mm"
include "ulmuni.mm"
include "ax-gen.mm"
include "gen2.mm"
include "dffun2.mm"
include "mpbir2an.mm"
include "funfvbrb.mm"
include "ax-mp.mm"

theorem ulmdm
  let cS: class S
  let cF: class F
  let vi: setvar i
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cG: class G
  let cH: class H
  let vy: setvar y
  let vz: setvar z


  assert |- ( F e. dom ( ~~>u ` S ) <-> F ( ~~>u ` S ) ( ( ~~>u ` S ) ` F ) )

  proof
    cS
    culm
    cfv
    #
    wfun
    #
    cF
    @0
    cdm
    wcel
    cF
    cF
    @0
    cfv
    @0
    wbr
    wb
    @1
    @0
    wrel
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    @2
    vz
    cv
    #
    @0
    wbr
    wa
    vy
    vz
    weq
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    cS
    ulmrel
    @6
    vx
    vy
    @5
    vz
    cS
    @2
    @3
    @4
    ulmuni
    ax-gen
    gen2
    vx
    vy
    vz
    @0
    dffun2
    mpbir2an
    cF
    @0
    funfvbrb
    ax-mp
end
