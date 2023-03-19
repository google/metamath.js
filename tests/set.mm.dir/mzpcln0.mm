include "cvv.mm"
include "wcel.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cmzpcl.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "mzpclall.mm"
include "ne0i.mm"
include "syl.mm"

theorem mzpcln0
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( V e. _V -> ( mzPolyCld ` V ) =/= (/) )

  proof
    cV
    cvv
    wcel
    cz
    cz
    cV
    cmap
    co
    cmap
    co
    #
    cV
    cmzpcl
    cfv
    #
    wcel
    @1
    c0
    wne
    cV
    mzpclall
    @1
    @0
    ne0i
    syl
end
