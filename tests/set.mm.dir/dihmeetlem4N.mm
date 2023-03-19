include "coc.mm"
include "cfv.mm"
include "ctrl.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "eqid.mm"
include "dihmeetlem4preN.mm"

theorem dihmeetlem4N
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let vh: setvar h
  let cT: class T
  let cP: class P
  assume dihmeetlem4.b: |- B = ( Base ` K )
  assume dihmeetlem4.l: |- .<_ = ( le ` K )
  assume dihmeetlem4.m: |- ./\ = ( meet ` K )
  assume dihmeetlem4.a: |- A = ( Atoms ` K )
  assume dihmeetlem4.h: |- H = ( LHyp ` K )
  assume dihmeetlem4.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem4.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem4.z: |- .0. = ( 0g ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( ( I ` Q ) i^i ( I ` ( X ./\ W ) ) ) = { .0. } )

  proof
    cA
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    cQ
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    vg
    vh
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @0
    vg
    cv
    cfv
    cQ
    wceq
    vg
    @2
    crio
    #
    cH
    cI
    cK
    c.le
    c.an
    vh
    @2
    cid
    cB
    cres
    cmpt
    #
    cW
    cX
    c.0
    dihmeetlem4.b
    dihmeetlem4.l
    dihmeetlem4.m
    dihmeetlem4.a
    dihmeetlem4.h
    dihmeetlem4.i
    dihmeetlem4.u
    dihmeetlem4.z
    @4
    eqid
    @0
    eqid
    @2
    eqid
    @1
    eqid
    @3
    eqid
    @5
    eqid
    dihmeetlem4preN
end
