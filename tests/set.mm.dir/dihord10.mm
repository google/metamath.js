include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "wceq.mm"
include "weq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31l.mm"
include "simp31r.mm"
include "simp33.mm"
include "dihordlem7b.mm"
include "simpld.mm"
include "syl123anc.mm"
include "fveq2d.mm"
include "simp32.mm"
include "eqbrtrd.mm"

theorem dihord10
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume dihjust.b: |- B = ( Base ` K )
  assume dihjust.l: |- .<_ = ( le ` K )
  assume dihjust.j: |- .\/ = ( join ` K )
  assume dihjust.m: |- ./\ = ( meet ` K )
  assume dihjust.a: |- A = ( Atoms ` K )
  assume dihjust.h: |- H = ( LHyp ` K )
  assume dihjust.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dihjust.J: |- J = ( ( DIsoC ` K ) ` W )
  assume dihjust.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjust.s: |- .(+) = ( LSSum ` U )
  assume dihord2c.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihord2c.r: |- R = ( ( trL ` K ) ` W )
  assume dihord2c.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dihord2.p: |- P = ( ( oc ` K ) ` W )
  assume dihord2.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihord2.d: |- .+ = ( +g ` U )
  assume dihord2.g: |- G = ( iota_ h e. T ( h ` P ) = N )

  disjoint f g
  disjoint f s
  disjoint .\/ f
  disjoint g s
  disjoint .\/ g
  disjoint .\/ s
  disjoint ./\ f
  disjoint ./\ g
  disjoint ./\ s
  disjoint .(+) f
  disjoint .(+) g
  disjoint .(+) s
  disjoint E g
  disjoint E s
  disjoint .+ g
  disjoint .+ s
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint h s
  disjoint A h
  disjoint A s
  disjoint I f
  disjoint I g
  disjoint I s
  disjoint J f
  disjoint J g
  disjoint J s
  disjoint G g
  disjoint O g
  disjoint O s
  disjoint P h
  disjoint Q f
  disjoint Q g
  disjoint Q s
  disjoint R f
  disjoint R g
  disjoint R s
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H s
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint K s
  disjoint .<_ f
  disjoint .<_ g
  disjoint .<_ h
  disjoint .<_ s
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint N s
  disjoint T f
  disjoint T g
  disjoint T h
  disjoint T s
  disjoint W f
  disjoint W g
  disjoint W h
  disjoint W s
  disjoint X f
  disjoint X g
  disjoint X s
  disjoint Y f
  disjoint Y g
  disjoint Y s
  disjoint f y
  disjoint f z
  disjoint g y
  disjoint g z
  disjoint s y
  disjoint s z
  disjoint y z
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ y
  disjoint ./\ z
  disjoint .(+) y
  disjoint .(+) z
  disjoint .+ y
  disjoint .+ z
  disjoint h y
  disjoint h z
  disjoint A y
  disjoint A z
  disjoint I y
  disjoint I z
  disjoint J y
  disjoint J z
  disjoint O y
  disjoint O z
  disjoint Q y
  disjoint Q z
  disjoint R y
  disjoint R z
  disjoint B y
  disjoint B z
  disjoint H y
  disjoint H z
  disjoint K y
  disjoint K z
  disjoint U y
  disjoint U z
  disjoint .<_ y
  disjoint .<_ z
  disjoint N y
  disjoint N z
  disjoint T y
  disjoint T z
  disjoint W y
  disjoint W z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) ) /\ ( f e. T /\ ( R ` f ) .<_ ( X ./\ W ) ) /\ ( ( s e. E /\ g e. T ) /\ ( R ` g ) .<_ ( Y ./\ W ) /\ <. f , O >. = ( <. ( s ` G ) , s >. .+ <. g , O >. ) ) ) -> ( R ` f ) .<_ ( Y ./\ W ) )

  proof
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
    cN
    cA
    wcel
    cN
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    vf
    cv
    #
    cT
    wcel
    @4
    cR
    cfv
    #
    cX
    cW
    c.an
    co
    c.le
    wbr
    wa
    #
    vs
    cv
    #
    cE
    wcel
    #
    vg
    cv
    #
    cT
    wcel
    #
    wa
    #
    @9
    cR
    cfv
    #
    cY
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @4
    cO
    cop
    cG
    @7
    cfv
    @7
    cop
    @9
    cO
    cop
    c.pl
    co
    wceq
    #
    w3a
    #
    w3a
    #
    @5
    @12
    @13
    c.le
    @17
    @4
    @9
    cR
    @17
    @0
    @1
    @2
    @8
    @10
    @15
    vf
    vg
    weq
    #
    @0
    @1
    @2
    @6
    @16
    simp11
    @0
    @1
    @2
    @6
    @16
    simp12
    @0
    @1
    @2
    @6
    @16
    simp13
    @8
    @10
    @14
    @15
    @3
    @6
    simp31l
    @8
    @10
    @14
    @15
    @3
    @6
    simp31r
    @3
    @6
    @11
    @14
    @15
    simp33
    @0
    @1
    @2
    wa
    @8
    @10
    @15
    w3a
    w3a
    @18
    cO
    @7
    wceq
    cA
    cB
    cP
    c.pl
    cQ
    cN
    cT
    cU
    vf
    vg
    vh
    cE
    cG
    cH
    cK
    c.le
    cO
    cW
    vs
    dihjust.b
    dihjust.l
    dihjust.a
    dihjust.h
    dihord2.p
    dihord2c.o
    dihord2c.t
    dihord2.e
    dihjust.u
    dihord2.d
    dihord2.g
    dihordlem7b
    simpld
    syl123anc
    fveq2d
    @3
    @6
    @11
    @14
    @15
    simp32
    eqbrtrd
end
