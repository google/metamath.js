include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "cmpt.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "cspr.mm"
include "cfv.mm"
include "cpw.mm"
include "fvex.mm"
include "pwex.mm"
include "eqeltri.mm"
include "mptexg.mm"
include "mp1i.mm"
include "eqid.mm"
include "sprsymrelf1o.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "sylc.mm"

theorem sprbisymrel
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vp: setvar p
  let vc: setvar c
  let vk: setvar k
  assume sprsymrelf.p: |- P = ~P ( Pairs ` V )
  assume sprsymrelf.r: |- R = { r e. ~P ( V X. V ) | A. x e. V A. y e. V ( x r y <-> y r x ) }

  disjoint V x
  disjoint V y
  disjoint x y
  disjoint r x
  disjoint r y
  disjoint f x
  disjoint f y
  disjoint P f
  disjoint R f
  disjoint V r
  disjoint W x
  disjoint W y
  disjoint P p
  disjoint V c
  disjoint c x
  disjoint c y
  disjoint c p
  disjoint p x
  disjoint p y
  disjoint c r
  disjoint p r
  disjoint c f
  disjoint f p
  disjoint R p
  disjoint W c
  disjoint k x
  assert |- ( V e. W -> E. f f : P -1-1-onto-> R )

  proof
    cV
    cW
    wcel
    #
    vp
    cP
    vc
    cv
    vx
    cv
    vy
    cv
    cpr
    wceq
    vc
    vp
    cv
    wrex
    vx
    vy
    copab
    #
    cmpt
    #
    cvv
    wcel
    #
    cP
    cR
    @2
    wf1o
    #
    cP
    cR
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    cP
    cvv
    wcel
    @3
    @0
    cP
    cV
    cspr
    cfv
    #
    cpw
    cvv
    sprsymrelf.p
    @7
    cV
    cspr
    fvex
    pwex
    eqeltri
    vp
    cP
    @1
    cvv
    mptexg
    mp1i
    vx
    vy
    cP
    cR
    @2
    cV
    cW
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    @2
    eqid
    sprsymrelf1o
    @6
    @4
    vf
    @2
    cvv
    cP
    cR
    @5
    @2
    f1oeq1
    spcegv
    sylc
end
