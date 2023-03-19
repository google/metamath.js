include "cv.mm"
include "dvhlvec.mm"
include "dochexmidlem1.mm"
include "lsatexch1.mm"
include "dochexmidlem2.mm"

theorem dochexmidlem3
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume dochexmidlem1.h: |- H = ( LHyp ` K )
  assume dochexmidlem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmidlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmidlem1.v: |- V = ( Base ` U )
  assume dochexmidlem1.s: |- S = ( LSubSp ` U )
  assume dochexmidlem1.n: |- N = ( LSpan ` U )
  assume dochexmidlem1.p: |- .(+) = ( LSSum ` U )
  assume dochexmidlem1.a: |- A = ( LSAtoms ` U )
  assume dochexmidlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmidlem1.x: |- ( ph -> X e. S )
  assume dochexmidlem3.pp: |- ( ph -> p e. A )
  assume dochexmidlem3.qq: |- ( ph -> q e. A )
  assume dochexmidlem3.rr: |- ( ph -> r e. A )
  assume dochexmidlem3.ql: |- ( ph -> q C_ ( ._|_ ` X ) )
  assume dochexmidlem3.rl: |- ( ph -> r C_ X )
  assume dochexmidlem3.pl: |- ( ph -> q C_ ( r .(+) p ) )


  assert |- ( ph -> p C_ ( X .(+) ( ._|_ ` X ) ) )

  proof
    wph
    cA
    c.po
    cS
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    vr
    vq
    vp
    dochexmidlem1.h
    dochexmidlem1.o
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.n
    dochexmidlem1.p
    dochexmidlem1.a
    dochexmidlem1.k
    dochexmidlem1.x
    dochexmidlem3.pp
    dochexmidlem3.qq
    dochexmidlem3.rr
    dochexmidlem3.ql
    dochexmidlem3.rl
    wph
    cA
    c.po
    vq
    cv
    vp
    cv
    vr
    cv
    cU
    dochexmidlem1.p
    dochexmidlem1.a
    wph
    cU
    cH
    cK
    cW
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.k
    dvhlvec
    dochexmidlem3.qq
    dochexmidlem3.pp
    dochexmidlem3.rr
    dochexmidlem3.pl
    wph
    cA
    c.po
    cS
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    vr
    vq
    vp
    dochexmidlem1.h
    dochexmidlem1.o
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.n
    dochexmidlem1.p
    dochexmidlem1.a
    dochexmidlem1.k
    dochexmidlem1.x
    dochexmidlem3.pp
    dochexmidlem3.qq
    dochexmidlem3.rr
    dochexmidlem3.ql
    dochexmidlem3.rl
    dochexmidlem1
    lsatexch1
    dochexmidlem2
end
