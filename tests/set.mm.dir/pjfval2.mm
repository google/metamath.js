include "clss.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "cbs.mm"
include "cmap.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cdm.mm"
include "df-mpt.mm"
include "df-xp.mm"
include "ineq12i.mm"
include "eqid.mm"
include "pjfval.mm"
include "wf.mm"
include "pjdm.mm"
include "eleq1.mm"
include "fvex.mm"
include "elmap.mm"
include "syl6rbb.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "pm5.32ri.mm"
include "an32.mm"
include "vex.mm"
include "biantrur.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "opabbii.mm"
include "inopab.mm"
include "3eqtr4i.mm"

theorem pjfval2
  let vx: setvar x
  let cP: class P
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let vy: setvar y
  let cT: class T
  assume pjfval2.o: |- ._|_ = ( ocv ` W )
  assume pjfval2.p: |- P = ( proj1 ` W )
  assume pjfval2.k: |- K = ( proj ` W )

  disjoint K x
  disjoint ._|_ x
  disjoint P x
  disjoint W x
  disjoint x y
  disjoint K y
  disjoint ._|_ y
  disjoint P y
  disjoint T x
  disjoint W y
  assert |- K = ( x e. dom K |-> ( x P ( ._|_ ` x ) ) )

  proof
    vx
    cW
    clss
    cfv
    #
    vx
    cv
    #
    @1
    c.pe
    cfv
    cP
    co
    #
    cmpt
    #
    cvv
    cW
    cbs
    cfv
    #
    @4
    cmap
    co
    #
    cxp
    #
    cin
    @1
    @0
    wcel
    #
    vy
    cv
    #
    @2
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    cvv
    wcel
    #
    @8
    @5
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cin
    #
    cK
    vx
    cK
    cdm
    #
    @2
    cmpt
    #
    @3
    @11
    @6
    @15
    vx
    vy
    @0
    @2
    df-mpt
    vx
    vy
    cvv
    @5
    df-xp
    ineq12i
    vx
    cP
    cK
    @0
    c.pe
    @4
    cW
    @4
    eqid
    #
    @0
    eqid
    #
    pjfval2.o
    pjfval2.p
    pjfval2.k
    pjfval
    @1
    @17
    wcel
    #
    @9
    wa
    #
    vx
    vy
    copab
    @10
    @14
    wa
    #
    vx
    vy
    copab
    @18
    @16
    @22
    @23
    vx
    vy
    @22
    @7
    @13
    wa
    #
    @9
    wa
    @10
    @13
    wa
    @23
    @9
    @21
    @24
    @21
    @7
    @4
    @4
    @2
    wf
    #
    wa
    @9
    @24
    cP
    @1
    cK
    @0
    c.pe
    @4
    cW
    @19
    @20
    pjfval2.o
    pjfval2.p
    pjfval2.k
    pjdm
    @9
    @25
    @13
    @7
    @9
    @13
    @2
    @5
    wcel
    @25
    @8
    @2
    @5
    eleq1
    @4
    @4
    @2
    cW
    cbs
    fvex
    #
    @26
    elmap
    syl6rbb
    anbi2d
    syl5bb
    pm5.32ri
    @7
    @13
    @9
    an32
    @13
    @14
    @10
    @12
    @13
    vx
    vex
    biantrur
    anbi2i
    3bitri
    opabbii
    vx
    vy
    @17
    @2
    df-mpt
    @10
    @14
    vx
    vy
    inopab
    3eqtr4i
    3eqtr4i
end
