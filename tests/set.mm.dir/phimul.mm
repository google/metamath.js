include "cn.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "cmul.mm"
include "cfzo.mm"
include "cxp.mm"
include "cv.mm"
include "crab.mm"
include "cmo.mm"
include "cop.mm"
include "cmpt.mm"
include "eqid.mm"
include "id.mm"
include "phimullem.mm"

theorem phimul
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( M e. NN /\ N e. NN /\ ( M gcd N ) = 1 ) -> ( phi ` ( M x. N ) ) = ( ( phi ` M ) x. ( phi ` N ) ) )

  proof
    cM
    cn
    wcel
    cN
    cn
    wcel
    cM
    cN
    cgcd
    co
    c1
    wceq
    w3a
    #
    vx
    vy
    cc0
    cM
    cN
    cmul
    co
    #
    cfzo
    co
    #
    cc0
    cM
    cfzo
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cxp
    #
    vy
    cv
    #
    cM
    cgcd
    co
    c1
    wceq
    vy
    @3
    crab
    #
    vx
    @2
    vx
    cv
    #
    cM
    cmo
    co
    @8
    cN
    cmo
    co
    cop
    cmpt
    #
    cM
    cN
    @6
    cN
    cgcd
    co
    c1
    wceq
    vy
    @4
    crab
    #
    @6
    @1
    cgcd
    co
    c1
    wceq
    vy
    @2
    crab
    #
    @2
    eqid
    @5
    eqid
    @9
    eqid
    @0
    id
    @7
    eqid
    @10
    eqid
    @11
    eqid
    phimullem
end
