include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfg.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-fg.mm"
include "a1i.mm"
include "wa.mm"
include "pweq.mm"
include "adantr.mm"
include "wb.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "adantl.mm"
include "rabeqbidv.mm"
include "fveq2.mm"
include "elfvex.mm"
include "id.mm"
include "cdm.mm"
include "elfvdm.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "ovmpt2dx.mm"

theorem fgval
  let vx: setvar x
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vv: setvar v

  disjoint F x
  disjoint X x
  disjoint f v
  disjoint f x
  disjoint F f
  disjoint v x
  disjoint F v
  disjoint X f
  disjoint X v
  assert |- ( F e. ( fBas ` X ) -> ( X filGen F ) = { x e. ~P X | ( F i^i ~P x ) =/= (/) } )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    vv
    vf
    cX
    cF
    cvv
    vv
    cv
    #
    cfbas
    cfv
    #
    vf
    cv
    #
    vx
    cv
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @2
    cpw
    #
    crab
    #
    cF
    @5
    cin
    #
    c0
    wne
    #
    vx
    cX
    cpw
    #
    crab
    #
    cfg
    @0
    cvv
    cfg
    vv
    vf
    cvv
    @3
    @9
    cmpt2
    wceq
    @1
    vf
    vx
    vv
    df-fg
    a1i
    @2
    cX
    wceq
    #
    @4
    cF
    wceq
    #
    wa
    #
    @9
    @13
    wceq
    @1
    @16
    @7
    @11
    vx
    @8
    @12
    @14
    @8
    @12
    wceq
    @15
    @2
    cX
    pweq
    adantr
    @15
    @7
    @11
    wb
    @14
    @15
    @6
    @10
    c0
    @4
    cF
    @5
    ineq1
    neeq1d
    adantl
    rabeqbidv
    adantl
    @14
    @3
    @0
    wceq
    @1
    @2
    cX
    cfbas
    fveq2
    adantl
    cF
    cX
    cfbas
    elfvex
    @1
    id
    @1
    cX
    cfbas
    cdm
    #
    wcel
    @12
    cvv
    wcel
    @13
    cvv
    wcel
    cF
    cX
    cfbas
    elfvdm
    cX
    @17
    pwexg
    @11
    vx
    @12
    cvv
    rabexg
    3syl
    ovmpt2dx
end
