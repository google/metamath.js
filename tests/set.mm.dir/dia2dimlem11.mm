include "dia2dimlem10.mm"
include "dia2dimlem9.mm"

theorem dia2dimlem11
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y
  assume dia2dimlem11.l: |- .<_ = ( le ` K )
  assume dia2dimlem11.j: |- .\/ = ( join ` K )
  assume dia2dimlem11.m: |- ./\ = ( meet ` K )
  assume dia2dimlem11.a: |- A = ( Atoms ` K )
  assume dia2dimlem11.h: |- H = ( LHyp ` K )
  assume dia2dimlem11.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem11.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem11.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem11.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem11.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem11.n: |- N = ( LSpan ` Y )
  assume dia2dimlem11.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem11.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem11.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem11.f: |- ( ph -> F e. T )
  assume dia2dimlem11.uv: |- ( ph -> U =/= V )
  assume dia2dimlem11.fe: |- ( ph -> F e. ( I ` ( U .\/ V ) ) )


  assert |- ( ph -> F e. ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cA
    c.po
    cR
    cS
    cT
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cV
    cW
    cY
    dia2dimlem11.l
    dia2dimlem11.j
    dia2dimlem11.m
    dia2dimlem11.a
    dia2dimlem11.h
    dia2dimlem11.t
    dia2dimlem11.r
    dia2dimlem11.y
    dia2dimlem11.s
    dia2dimlem11.pl
    dia2dimlem11.n
    dia2dimlem11.i
    dia2dimlem11.k
    dia2dimlem11.u
    dia2dimlem11.v
    dia2dimlem11.f
    wph
    cA
    cR
    cS
    cT
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    cN
    cV
    cW
    cY
    dia2dimlem11.l
    dia2dimlem11.j
    dia2dimlem11.a
    dia2dimlem11.h
    dia2dimlem11.t
    dia2dimlem11.r
    dia2dimlem11.y
    dia2dimlem11.s
    dia2dimlem11.n
    dia2dimlem11.i
    dia2dimlem11.k
    dia2dimlem11.u
    dia2dimlem11.v
    dia2dimlem11.f
    dia2dimlem11.fe
    dia2dimlem10
    dia2dimlem11.uv
    dia2dimlem9
end
