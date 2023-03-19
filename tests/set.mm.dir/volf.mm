include "cvol.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cr.mm"
include "cpw.mm"
include "wss.mm"
include "wfun.mm"
include "cxp.mm"
include "wa.mm"
include "covol.mm"
include "cres.mm"
include "ovolf.mm"
include "ffun.mm"
include "funres.mm"
include "mp2b.mm"
include "volres.mm"
include "funeqi.mm"
include "mpbir.mm"
include "resss.mm"
include "eqsstri.mm"
include "fssxp.mm"
include "ax-mp.mm"
include "sstri.mm"
include "pm3.2i.mm"
include "funssxp.mm"
include "mpbi.mm"
include "simpli.mm"

theorem volf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- vol : dom vol --> ( 0 [,] +oo )

  proof
    cvol
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cvol
    wf
    #
    @0
    cr
    cpw
    #
    wss
    #
    cvol
    wfun
    #
    cvol
    @3
    @1
    cxp
    #
    wss
    #
    wa
    @2
    @4
    wa
    @5
    @7
    @5
    covol
    @0
    cres
    #
    wfun
    #
    @3
    @1
    covol
    wf
    #
    covol
    wfun
    @9
    ovolf
    @3
    @1
    covol
    ffun
    @0
    covol
    funres
    mp2b
    cvol
    @8
    volres
    funeqi
    mpbir
    cvol
    covol
    @6
    cvol
    @8
    covol
    volres
    covol
    @0
    resss
    eqsstri
    @10
    covol
    @6
    wss
    ovolf
    @3
    @1
    covol
    fssxp
    ax-mp
    sstri
    pm3.2i
    @3
    @1
    cvol
    funssxp
    mpbi
    simpli
end
