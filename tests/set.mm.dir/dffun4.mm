include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "cop.mm"
include "wcel.mm"
include "dffun2.mm"
include "df-br.mm"
include "anbi12i.mm"
include "imbi1i.mm"
include "albii.mm"
include "2albii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( Fun A <-> ( Rel A /\ A. x A. y A. z ( ( <. x , y >. e. A /\ <. x , z >. e. A ) -> y = z ) ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    wa
    @0
    @1
    @2
    cop
    cA
    wcel
    #
    @1
    @4
    cop
    cA
    wcel
    #
    wa
    #
    @7
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    wa
    vx
    vy
    vz
    cA
    dffun2
    @10
    @16
    @0
    @9
    @15
    vx
    vy
    @8
    @14
    vz
    @6
    @13
    @7
    @3
    @11
    @5
    @12
    @1
    @2
    cA
    df-br
    @1
    @4
    cA
    df-br
    anbi12i
    imbi1i
    albii
    2albii
    anbi2i
    bitri
end
