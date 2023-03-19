include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "co1.mm"
include "eldmg.mm"
include "ibi.mm"
include "rlimo1.mm"
include "exlimiv.mm"
include "syl.mm"

theorem rlimdmo1
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let cG: class G


  assert |- ( F e. dom ~~>r -> F e. O(1) )

  proof
    cF
    crli
    cdm
    #
    wcel
    #
    cF
    vx
    cv
    #
    crli
    wbr
    #
    vx
    wex
    #
    cF
    co1
    wcel
    #
    @1
    @4
    vx
    cF
    crli
    @0
    eldmg
    ibi
    @3
    @5
    vx
    @2
    cF
    rlimo1
    exlimiv
    syl
end
