include "cv.mm"
include "dihmeetlem12N.mm"

theorem dihmeetlem14N
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
  let cY: class Y
  let vr: setvar r
  let vp: setvar p
  let vh: setvar h
  assume dihmeetlem14.b: |- B = ( Base ` K )
  assume dihmeetlem14.l: |- .<_ = ( le ` K )
  assume dihmeetlem14.h: |- H = ( LHyp ` K )
  assume dihmeetlem14.j: |- .\/ = ( join ` K )
  assume dihmeetlem14.m: |- ./\ = ( meet ` K )
  assume dihmeetlem14.a: |- A = ( Atoms ` K )
  assume dihmeetlem14.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem14.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem14.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ Y e. B /\ p e. B ) /\ ( ( r e. A /\ -. r .<_ W ) /\ r .<_ Y /\ ( Y ./\ p ) .<_ W ) ) -> ( ( I ` ( Y ./\ p ) ) .(+) ( ( I ` r ) i^i ( I ` p ) ) ) = ( ( I ` Y ) i^i ( I ` p ) ) )

  proof
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cY
    vp
    cv
    vr
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.h
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.u
    dihmeetlem14.s
    dihmeetlem14.i
    dihmeetlem12N
end
