include "wcel.mm"
include "carw.mm"
include "cdm.mm"
include "ccat.mm"
include "cv.mm"
include "choma.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "df-arw.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "sseldi.mm"

theorem arwrcl
  let cA: class A
  let cC: class C
  let cF: class F
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let vc: setvar c
  assume arwrcl.a: |- A = ( Arrow ` C )


  assert |- ( F e. A -> C e. Cat )

  proof
    cF
    cA
    wcel
    carw
    cdm
    #
    ccat
    cC
    vc
    ccat
    vc
    cv
    choma
    cfv
    crn
    cuni
    carw
    vc
    df-arw
    dmmptss
    cC
    @0
    wcel
    cF
    cC
    carw
    cfv
    cA
    cF
    cC
    carw
    elfvdm
    arwrcl.a
    eleq2s
    sseldi
end
