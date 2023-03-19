include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cnop.mm"
include "chil.mm"
include "df-hba.mm"
include "eqid.mm"
include "hhnm.mm"
include "cnmoo.mm"
include "co.mm"
include "hhnmoi.mm"
include "hhnv.mm"
include "nmoub2i.mm"

theorem nmopub2tHIL
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S

  disjoint A x
  disjoint T x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T y
  disjoint T z
  disjoint T w
  assert |- ( ( T : ~H --> ~H /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. ~H ( normh ` ( T ` x ) ) <_ ( A x. ( normh ` x ) ) ) -> ( normop ` T ) <_ A )

  proof
    vx
    cA
    cT
    cva
    csm
    cop
    cno
    cop
    #
    cno
    cno
    cnop
    @0
    chil
    chil
    df-hba
    df-hba
    @0
    @0
    eqid
    #
    hhnm
    #
    @2
    @0
    @0
    @0
    cnmoo
    co
    #
    @1
    @3
    eqid
    hhnmoi
    @0
    @1
    hhnv
    #
    @4
    nmoub2i
end
