include "cc.mm"
include "wcel.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cim.mm"
include "cc0.mm"
include "wceq.mm"
include "sigarval.mm"
include "anidms.mm"
include "cr.mm"
include "cjcl.mm"
include "id.mm"
include "mulcomd.mm"
include "cjmulrcl.mm"
include "eqeltrd.mm"
include "reim0d.mm"
include "eqtrd.mm"

theorem sigarid
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cG: class G
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint k x
  assert |- ( A e. CC -> ( A G A ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cA
    cG
    co
    #
    cA
    ccj
    cfv
    #
    cA
    cmul
    co
    #
    cim
    cfv
    #
    cc0
    @0
    @1
    @4
    wceq
    vx
    vy
    cA
    cA
    cG
    sigar
    sigarval
    anidms
    @0
    @3
    @0
    @3
    cA
    @2
    cmul
    co
    cr
    @0
    @2
    cA
    cA
    cjcl
    @0
    id
    mulcomd
    cA
    cjmulrcl
    eqeltrd
    reim0d
    eqtrd
end
