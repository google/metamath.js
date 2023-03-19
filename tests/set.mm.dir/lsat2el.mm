include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "eqid.mm"
include "lsatel.mm"
include "eqtr4d.mm"

theorem lsat2el
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lsat2el.o: |- .0. = ( 0g ` W )
  assume lsat2el.a: |- A = ( LSAtoms ` W )
  assume lsat2el.w: |- ( ph -> W e. LVec )
  assume lsat2el.p: |- ( ph -> P e. A )
  assume lsat2el.q: |- ( ph -> Q e. A )
  assume lsat2el.x: |- ( ph -> X =/= .0. )
  assume lsat2el.x1: |- ( ph -> X e. P )
  assume lsat2el.x2: |- ( ph -> X e. Q )


  assert |- ( ph -> P = Q )

  proof
    wph
    cP
    cX
    csn
    cW
    clspn
    cfv
    #
    cfv
    cQ
    wph
    cA
    cP
    @0
    cW
    cX
    c.0
    lsat2el.o
    @0
    eqid
    #
    lsat2el.a
    lsat2el.w
    lsat2el.p
    lsat2el.x1
    lsat2el.x
    lsatel
    wph
    cA
    cQ
    @0
    cW
    cX
    c.0
    lsat2el.o
    @1
    lsat2el.a
    lsat2el.w
    lsat2el.q
    lsat2el.x2
    lsat2el.x
    lsatel
    eqtr4d
end
