include "chil.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "chot.mm"
include "co.mm"
include "chod.mm"
include "wf1.mm"
include "wn.mm"
include "cc.mm"
include "crab.mm"
include "cspc.mm"
include "cnex.mm"
include "rabex.mm"
include "ax-hilex.mm"
include "wceq.mm"
include "wb.mm"
include "oveq1.mm"
include "f1eq1.mm"
include "syl.mm"
include "notbid.mm"
include "rabbidv.mm"
include "df-spec.mm"
include "fvmptmap.mm"

theorem specval
  let vx: setvar x
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint T x
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T y
  disjoint T z
  assert |- ( T : ~H --> ~H -> ( Lambda ` T ) = { x e. CC | -. ( T -op ( x .op ( _I |` ~H ) ) ) : ~H -1-1-> ~H } )

  proof
    vt
    cT
    chil
    chil
    vt
    cv
    #
    vx
    cv
    cid
    chil
    cres
    chot
    co
    #
    chod
    co
    #
    wf1
    #
    wn
    #
    vx
    cc
    crab
    chil
    chil
    cT
    @1
    chod
    co
    #
    wf1
    #
    wn
    #
    vx
    cc
    crab
    chil
    chil
    cspc
    @7
    vx
    cc
    cnex
    rabex
    ax-hilex
    ax-hilex
    @0
    cT
    wceq
    #
    @4
    @7
    vx
    cc
    @8
    @3
    @6
    @8
    @2
    @5
    wceq
    @3
    @6
    wb
    @0
    cT
    @1
    chod
    oveq1
    chil
    chil
    @2
    @5
    f1eq1
    syl
    notbid
    rabbidv
    vx
    vt
    df-spec
    fvmptmap
end
