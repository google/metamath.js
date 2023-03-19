include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cop.mm"
include "cmo.mm"
include "co.mm"
include "cif.mm"
include "cn0.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "wa.mm"
include "cn.mm"
include "wne.mm"
include "nnne0.mm"
include "adantl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "nnnn0.mm"
include "cz.mm"
include "nn0z.mm"
include "zmodcl.mm"
include "sylan.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "iftrue.mm"
include "adantr.mm"
include "wo.mm"
include "simpr.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "rgen2a.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem eucalgf
  let vx: setvar x
  let vy: setvar y
  let cE: class E
  let cM: class M
  let cN: class N
  let cX: class X
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume eucalgval.1: |- E = ( x e. NN0 , y e. NN0 |-> if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R z
  disjoint E z
  assert |- E : ( NN0 X. NN0 ) --> ( NN0 X. NN0 )

  proof
    vy
    cv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    @0
    cop
    #
    @0
    @2
    @0
    cmo
    co
    #
    cop
    #
    cif
    #
    cn0
    cn0
    cxp
    #
    wcel
    #
    vy
    cn0
    wral
    vx
    cn0
    wral
    @7
    @7
    cE
    wf
    @8
    vx
    vy
    cn0
    @2
    cn0
    wcel
    #
    @0
    cn0
    wcel
    #
    wa
    #
    @0
    cn
    wcel
    #
    @8
    @1
    @9
    @12
    @8
    @10
    @9
    @12
    wa
    #
    @6
    @5
    @7
    @13
    @1
    @3
    @5
    @13
    @0
    cc0
    @12
    @0
    cc0
    wne
    @9
    @0
    nnne0
    adantl
    neneqd
    iffalsed
    @13
    @10
    @4
    cn0
    wcel
    #
    @5
    @7
    wcel
    @12
    @10
    @9
    @0
    nnnn0
    adantl
    @9
    @2
    cz
    wcel
    @12
    @14
    @2
    nn0z
    @2
    @0
    zmodcl
    sylan
    @0
    @4
    cn0
    cn0
    opelxpi
    syl2anc
    eqeltrd
    adantlr
    @11
    @1
    wa
    @6
    @3
    @7
    @1
    @6
    @3
    wceq
    @11
    @1
    @3
    @5
    iftrue
    adantl
    @11
    @3
    @7
    wcel
    @1
    @2
    @0
    cn0
    cn0
    opelxpi
    adantr
    eqeltrd
    @11
    @10
    @12
    @1
    wo
    @9
    @10
    simpr
    @0
    elnn0
    sylib
    mpjaodan
    rgen2a
    vx
    vy
    cn0
    cn0
    @6
    @7
    cE
    eucalgval.1
    fmpt2
    mpbi
end
