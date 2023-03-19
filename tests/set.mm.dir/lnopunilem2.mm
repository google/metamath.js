include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cmul.mm"
include "cre.mm"
include "wceq.mm"
include "cc.mm"
include "wral.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "0cn.mm"
include "elimel.mm"
include "lnopunilem1.mm"
include "dedth.mm"
include "rgen.mm"
include "wb.mm"
include "chil.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "ax-mp.mm"
include "hicli.mm"
include "recan.mm"
include "mp2an.mm"
include "mpbi.mm"

theorem lnopunilem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vy: setvar y
  let cC: class C
  assume lnopunilem.1: |- T e. LinOp
  assume lnopunilem.2: |- A. x e. ~H ( normh ` ( T ` x ) ) = ( normh ` x )
  assume lnopunilem.3: |- A e. ~H
  assume lnopunilem.4: |- B e. ~H

  disjoint T x
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint x y
  disjoint T y
  assert |- ( ( T ` A ) .ih ( T ` B ) ) = ( A .ih B )

  proof
    vy
    cv
    #
    cA
    cT
    cfv
    #
    cB
    cT
    cfv
    #
    csp
    co
    #
    cmul
    co
    #
    cre
    cfv
    #
    @0
    cA
    cB
    csp
    co
    #
    cmul
    co
    #
    cre
    cfv
    #
    wceq
    #
    vy
    cc
    wral
    #
    @3
    @6
    wceq
    #
    @9
    vy
    cc
    @0
    cc
    wcel
    #
    @9
    @12
    @0
    cc0
    cif
    #
    @3
    cmul
    co
    #
    cre
    cfv
    #
    @13
    @6
    cmul
    co
    #
    cre
    cfv
    #
    wceq
    @0
    cc0
    @0
    @13
    wceq
    #
    @5
    @15
    @8
    @17
    @18
    @4
    @14
    cre
    @0
    @13
    @3
    cmul
    oveq1
    fveq2d
    @18
    @7
    @16
    cre
    @0
    @13
    @6
    cmul
    oveq1
    fveq2d
    eqeq12d
    vx
    cA
    cB
    @13
    cT
    lnopunilem.1
    lnopunilem.2
    lnopunilem.3
    lnopunilem.4
    @0
    cc0
    cc
    0cn
    elimel
    lnopunilem1
    dedth
    rgen
    @3
    cc
    wcel
    @6
    cc
    wcel
    @10
    @11
    wb
    @1
    @2
    cA
    chil
    wcel
    @1
    chil
    wcel
    lnopunilem.3
    chil
    chil
    cA
    cT
    cT
    lnopunilem.1
    lnopfi
    #
    ffvelrni
    ax-mp
    cB
    chil
    wcel
    @2
    chil
    wcel
    lnopunilem.4
    chil
    chil
    cB
    cT
    @19
    ffvelrni
    ax-mp
    hicli
    cA
    cB
    lnopunilem.3
    lnopunilem.4
    hicli
    vy
    @3
    @6
    recan
    mp2an
    mpbi
end
