include "coc.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "lhpocnel.mm"
include "syl.mm"
include "dia2dimlem7.mm"

theorem dia2dimlem8
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
  assume dia2dimlem8.l: |- .<_ = ( le ` K )
  assume dia2dimlem8.j: |- .\/ = ( join ` K )
  assume dia2dimlem8.m: |- ./\ = ( meet ` K )
  assume dia2dimlem8.a: |- A = ( Atoms ` K )
  assume dia2dimlem8.h: |- H = ( LHyp ` K )
  assume dia2dimlem8.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem8.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem8.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem8.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem8.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem8.n: |- N = ( LSpan ` Y )
  assume dia2dimlem8.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem8.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem8.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem8.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem8.f: |- ( ph -> F e. T )
  assume dia2dimlem8.rf: |- ( ph -> ( R ` F ) .<_ ( U .\/ V ) )
  assume dia2dimlem8.uv: |- ( ph -> U =/= V )
  assume dia2dimlem8.ru: |- ( ph -> ( R ` F ) =/= U )
  assume dia2dimlem8.rv: |- ( ph -> ( R ` F ) =/= V )


  assert |- ( ph -> F e. ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cA
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    c.po
    @1
    cU
    c.or
    co
    @1
    cF
    cfv
    cV
    c.or
    co
    c.an
    co
    #
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
    dia2dimlem8.l
    dia2dimlem8.j
    dia2dimlem8.m
    dia2dimlem8.a
    dia2dimlem8.h
    dia2dimlem8.t
    dia2dimlem8.r
    dia2dimlem8.y
    dia2dimlem8.s
    dia2dimlem8.pl
    dia2dimlem8.n
    dia2dimlem8.i
    @2
    eqid
    dia2dimlem8.k
    dia2dimlem8.u
    dia2dimlem8.v
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    cA
    wcel
    @1
    cW
    c.le
    wbr
    wn
    wa
    dia2dimlem8.k
    cA
    cH
    cK
    c.le
    @0
    cW
    dia2dimlem8.l
    @0
    eqid
    dia2dimlem8.a
    dia2dimlem8.h
    lhpocnel
    syl
    dia2dimlem8.f
    dia2dimlem8.rf
    dia2dimlem8.uv
    dia2dimlem8.ru
    dia2dimlem8.rv
    dia2dimlem7
end
