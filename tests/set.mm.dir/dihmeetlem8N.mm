include "cv.mm"
include "dihjatc1.mm"

theorem dihmeetlem8N
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume dihmeetlem8.b: |- B = ( Base ` K )
  assume dihmeetlem8.l: |- .<_ = ( le ` K )
  assume dihmeetlem8.h: |- H = ( LHyp ` K )
  assume dihmeetlem8.j: |- .\/ = ( join ` K )
  assume dihmeetlem8.m: |- ./\ = ( meet ` K )
  assume dihmeetlem8.a: |- A = ( Atoms ` K )
  assume dihmeetlem8.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem8.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem8.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( p e. A /\ -. p .<_ W ) /\ ( p .<_ X /\ ( X ./\ Y ) .<_ W ) ) -> ( I ` ( ( X ./\ Y ) .\/ p ) ) = ( ( I ` p ) .(+) ( I ` ( X ./\ Y ) ) ) )

  proof
    cA
    cB
    c.po
    vp
    cv
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    dihmeetlem8.b
    dihmeetlem8.l
    dihmeetlem8.h
    dihmeetlem8.j
    dihmeetlem8.m
    dihmeetlem8.a
    dihmeetlem8.u
    dihmeetlem8.s
    dihmeetlem8.i
    dihjatc1
end
