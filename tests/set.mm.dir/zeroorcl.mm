include "ccat.mm"
include "cv.mm"
include "cinito.mm"
include "cfv.mm"
include "ctermo.mm"
include "cin.mm"
include "czeroo.mm"
include "df-zeroo.mm"
include "mptrcl.mm"

theorem zeroorcl
  let cC: class C
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h


  assert |- ( Z e. ( ZeroO ` C ) -> C e. Cat )

  proof
    vc
    ccat
    vc
    cv
    #
    cinito
    cfv
    @0
    ctermo
    cfv
    cin
    czeroo
    cZ
    cC
    vc
    df-zeroo
    mptrcl
end
