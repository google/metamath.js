include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "cop.mm"
include "wcel.mm"
include "dffun3.mm"
include "df-br.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun5
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
  assert |- ( Fun A <-> ( Rel A /\ A. x E. z A. y ( <. x , y >. e. A -> y = z ) ) )

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
    vy
    vz
    weq
    #
    wi
    #
    vy
    wal
    #
    vz
    wex
    #
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
    @4
    wi
    #
    vy
    wal
    #
    vz
    wex
    #
    vx
    wal
    #
    wa
    vx
    vy
    vz
    cA
    dffun3
    @8
    @13
    @0
    @7
    @12
    vx
    @6
    @11
    vz
    @5
    @10
    vy
    @3
    @9
    @4
    @1
    @2
    cA
    df-br
    imbi1i
    albii
    exbii
    albii
    anbi2i
    bitri
end
