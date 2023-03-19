include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "co.mm"
include "wcel.mm"
include "chlt.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "dia2dimlem1.mm"
include "wne.mm"
include "simpld.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "cdleme50ex.mm"
include "wi.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "dia2dimlem5.mm"
include "3exp.mm"
include "3expd.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem dia2dimlem6
  let wph: wff ph
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
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
  let vd: setvar d
  let vg: setvar g
  assume dia2dimlem6.l: |- .<_ = ( le ` K )
  assume dia2dimlem6.j: |- .\/ = ( join ` K )
  assume dia2dimlem6.m: |- ./\ = ( meet ` K )
  assume dia2dimlem6.a: |- A = ( Atoms ` K )
  assume dia2dimlem6.h: |- H = ( LHyp ` K )
  assume dia2dimlem6.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem6.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem6.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem6.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem6.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem6.n: |- N = ( LSpan ` Y )
  assume dia2dimlem6.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem6.q: |- Q = ( ( P .\/ U ) ./\ ( ( F ` P ) .\/ V ) )
  assume dia2dimlem6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem6.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem6.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem6.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dia2dimlem6.f: |- ( ph -> ( F e. T /\ ( F ` P ) =/= P ) )
  assume dia2dimlem6.rf: |- ( ph -> ( R ` F ) .<_ ( U .\/ V ) )
  assume dia2dimlem6.uv: |- ( ph -> U =/= V )
  assume dia2dimlem6.ru: |- ( ph -> ( R ` F ) =/= U )
  assume dia2dimlem6.rv: |- ( ph -> ( R ` F ) =/= V )


  assert |- ( ph -> F e. ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cQ
    vd
    cv
    #
    cfv
    cP
    cF
    cfv
    #
    wceq
    #
    vd
    cT
    wrex
    #
    cF
    cU
    cI
    cfv
    cV
    cI
    cfv
    c.po
    co
    wcel
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    cA
    wcel
    @1
    cW
    c.le
    wbr
    wn
    wa
    #
    @3
    dia2dimlem6.k
    wph
    cA
    cP
    cQ
    cR
    cT
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    dia2dimlem6.l
    dia2dimlem6.j
    dia2dimlem6.m
    dia2dimlem6.a
    dia2dimlem6.h
    dia2dimlem6.t
    dia2dimlem6.r
    dia2dimlem6.q
    dia2dimlem6.k
    dia2dimlem6.u
    dia2dimlem6.v
    dia2dimlem6.p
    dia2dimlem6.f
    dia2dimlem6.rf
    dia2dimlem6.uv
    dia2dimlem6.ru
    dia2dimlem1
    #
    wph
    @5
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @7
    dia2dimlem6.k
    wph
    @9
    @1
    cP
    wne
    #
    dia2dimlem6.f
    simpld
    dia2dimlem6.p
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    dia2dimlem6.l
    dia2dimlem6.a
    dia2dimlem6.h
    dia2dimlem6.t
    ltrnel
    syl3anc
    cA
    cQ
    @1
    cT
    vd
    cH
    cK
    c.le
    cW
    dia2dimlem6.l
    dia2dimlem6.a
    dia2dimlem6.h
    dia2dimlem6.t
    cdleme50ex
    syl3anc
    wph
    @2
    @4
    vd
    cT
    wph
    cP
    vg
    cv
    #
    cfv
    cQ
    wceq
    #
    vg
    cT
    wrex
    #
    @0
    cT
    wcel
    #
    @2
    @4
    wi
    #
    wi
    #
    wph
    @5
    @10
    @6
    @14
    dia2dimlem6.k
    dia2dimlem6.p
    @8
    cA
    cP
    cQ
    cT
    vg
    cH
    cK
    c.le
    cW
    dia2dimlem6.l
    dia2dimlem6.a
    dia2dimlem6.h
    dia2dimlem6.t
    cdleme50ex
    syl3anc
    wph
    @13
    @17
    vg
    cT
    wph
    @12
    cT
    wcel
    #
    @13
    @15
    @16
    wph
    @18
    @13
    @15
    w3a
    #
    @2
    @4
    wph
    @19
    @2
    w3a
    cA
    @0
    cP
    c.po
    cQ
    cR
    cS
    cT
    cU
    cF
    @12
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
    dia2dimlem6.l
    dia2dimlem6.j
    dia2dimlem6.m
    dia2dimlem6.a
    dia2dimlem6.h
    dia2dimlem6.t
    dia2dimlem6.r
    dia2dimlem6.y
    dia2dimlem6.s
    dia2dimlem6.pl
    dia2dimlem6.n
    dia2dimlem6.i
    dia2dimlem6.q
    wph
    @19
    @5
    @2
    dia2dimlem6.k
    3ad2ant1
    wph
    @19
    cU
    cA
    wcel
    cU
    cW
    c.le
    wbr
    wa
    @2
    dia2dimlem6.u
    3ad2ant1
    wph
    @19
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    wa
    @2
    dia2dimlem6.v
    3ad2ant1
    wph
    @19
    @10
    @2
    dia2dimlem6.p
    3ad2ant1
    wph
    @19
    @9
    @11
    wa
    @2
    dia2dimlem6.f
    3ad2ant1
    wph
    @19
    cF
    cR
    cfv
    #
    cU
    cV
    c.or
    co
    c.le
    wbr
    @2
    dia2dimlem6.rf
    3ad2ant1
    wph
    @19
    cU
    cV
    wne
    @2
    dia2dimlem6.uv
    3ad2ant1
    wph
    @19
    @20
    cU
    wne
    @2
    dia2dimlem6.ru
    3ad2ant1
    wph
    @19
    @20
    cV
    wne
    @2
    dia2dimlem6.rv
    3ad2ant1
    wph
    @18
    @13
    @15
    @2
    simp21
    wph
    @18
    @13
    @15
    @2
    simp22
    wph
    @18
    @13
    @15
    @2
    simp23
    wph
    @19
    @2
    simp3
    dia2dimlem5
    3exp
    3expd
    rexlimdv
    mpd
    rexlimdv
    mpd
end
