include "cbs.mm"
include "cfv.mm"
include "catm.mm"
include "coc.mm"
include "ctrl.mm"
include "clss.mm"
include "cltrn.mm"
include "cvsca.mm"
include "ctendo.mm"
include "csca.mm"
include "cv.mm"
include "cinvr.mm"
include "wceq.mm"
include "crio.mm"
include "cple.mm"
include "clspn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "c0g.mm"
include "eqid.mm"
include "dih1dimatlem.mm"

theorem dih1dimat
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.le: class .<_
  let vh: setvar h
  let c.0: class .0.
  let vv: setvar v
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cE: class E
  let cF: class F
  let cC: class C
  let cD: class D
  let cG: class G
  let cJ: class J
  let cN: class N
  let cT: class T
  let cV: class V
  let cO: class O
  let c.x: class .x.
  assume dih1dimat.h: |- H = ( LHyp ` K )
  assume dih1dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1dimat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1dimat.a: |- A = ( LSAtoms ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ P e. A ) -> P e. ran I )

  proof
    cA
    cK
    cbs
    cfv
    #
    cK
    catm
    cfv
    #
    cP
    cW
    cK
    coc
    cfv
    cfv
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cU
    clss
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cvsca
    cfv
    #
    cU
    vf
    vh
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cU
    csca
    cfv
    #
    @2
    vh
    cv
    cfv
    @2
    vf
    cv
    vs
    cv
    @8
    cinvr
    cfv
    #
    cfv
    cfv
    cfv
    wceq
    vh
    @5
    crio
    #
    cH
    cI
    @9
    cK
    cK
    cple
    cfv
    #
    cU
    clspn
    cfv
    #
    vh
    @5
    cid
    @0
    cres
    cmpt
    #
    cU
    cbs
    cfv
    #
    cW
    cU
    c0g
    cfv
    #
    vs
    dih1dimat.h
    dih1dimat.u
    dih1dimat.i
    dih1dimat.a
    @0
    eqid
    @11
    eqid
    @1
    eqid
    @2
    eqid
    @5
    eqid
    @3
    eqid
    @7
    eqid
    @13
    eqid
    @8
    eqid
    @9
    eqid
    @14
    eqid
    @6
    eqid
    @4
    eqid
    @12
    eqid
    @15
    eqid
    @10
    eqid
    dih1dimatlem
end
