include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cnv.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cr.mm"
include "wss.mm"
include "eqid.mm"
include "hhnv.mm"
include "df-hba.mm"
include "hhnm.mm"
include "nmosetre.mm"
include "mpan.mm"

theorem nmopsetretHIL
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint T x
  disjoint T y
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
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T : ~H --> ~H -> { x | E. y e. ~H ( ( normh ` y ) <_ 1 /\ x = ( normh ` ( T ` y ) ) ) } C_ RR )

  proof
    cva
    csm
    cop
    cno
    cop
    #
    cnv
    wcel
    chil
    chil
    cT
    wf
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    vx
    cv
    @1
    cT
    cfv
    cno
    cfv
    wceq
    wa
    vy
    chil
    wrex
    vx
    cab
    cr
    wss
    @0
    @0
    eqid
    #
    hhnv
    vx
    vy
    cT
    cno
    cno
    @0
    chil
    chil
    df-hba
    @0
    @2
    hhnm
    nmosetre
    mpan
end
