include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "w3a.mm"
include "cop.mm"
include "wceq.mm"
include "simp3.mm"
include "eqidd.mm"
include "wb.mm"
include "simp1.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "dibopelval3.mm"
include "syl12anc.mm"
include "mpbir2and.mm"

theorem dihord2cN
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vh: setvar h
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let c.pl: class .+
  let cG: class G
  let cP: class P
  let cQ: class Q
  let cN: class N
  let cY: class Y
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

  disjoint .\/ f
  disjoint ./\ f
  disjoint .(+) f
  disjoint f h
  disjoint A f
  disjoint A h
  disjoint I f
  disjoint J f
  disjoint R f
  disjoint B f
  disjoint B h
  disjoint H f
  disjoint H h
  disjoint K f
  disjoint K h
  disjoint .<_ f
  disjoint .<_ h
  disjoint T f
  disjoint T h
  disjoint W f
  disjoint W h
  disjoint X f
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint f z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint .\/ g
  disjoint s y
  disjoint s z
  disjoint .\/ s
  disjoint y z
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ g
  disjoint ./\ s
  disjoint ./\ y
  disjoint ./\ z
  disjoint .(+) g
  disjoint .(+) s
  disjoint .(+) y
  disjoint .(+) z
  disjoint E g
  disjoint E s
  disjoint .+ g
  disjoint .+ s
  disjoint .+ y
  disjoint .+ z
  disjoint g h
  disjoint A g
  disjoint h s
  disjoint h y
  disjoint h z
  disjoint A s
  disjoint A y
  disjoint A z
  disjoint I g
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint J g
  disjoint J s
  disjoint J y
  disjoint J z
  disjoint G g
  disjoint O g
  disjoint O s
  disjoint O y
  disjoint O z
  disjoint P h
  disjoint Q f
  disjoint Q g
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint R g
  disjoint R s
  disjoint R y
  disjoint R z
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint H g
  disjoint H s
  disjoint H y
  disjoint H z
  disjoint K g
  disjoint K s
  disjoint K y
  disjoint K z
  disjoint U y
  disjoint U z
  disjoint .<_ g
  disjoint .<_ s
  disjoint .<_ y
  disjoint .<_ z
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint T g
  disjoint T s
  disjoint T y
  disjoint T z
  disjoint W g
  disjoint W s
  disjoint W y
  disjoint W z
  disjoint X g
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y s
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ ( f e. T /\ ( R ` f ) .<_ ( X ./\ W ) ) ) -> <. f , O >. e. ( I ` ( X ./\ W ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    vf
    cv
    #
    cT
    wcel
    @4
    cR
    cfv
    cX
    cW
    c.an
    co
    #
    c.le
    wbr
    wa
    #
    w3a
    #
    @4
    cO
    cop
    @5
    cI
    cfv
    wcel
    #
    @6
    cO
    cO
    wceq
    #
    @2
    @3
    @6
    simp3
    @7
    cO
    eqidd
    @7
    @2
    @5
    cB
    wcel
    #
    @5
    cW
    c.le
    wbr
    #
    @8
    @6
    @9
    wa
    wb
    @2
    @3
    @6
    simp1
    @7
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @10
    @7
    @0
    @12
    @0
    @1
    @3
    @6
    simp1l
    cK
    hllat
    syl
    #
    @2
    @3
    @6
    simp2
    #
    @7
    @1
    @13
    @0
    @1
    @3
    @6
    simp1r
    cB
    cH
    cK
    cW
    dihjust.b
    dihjust.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    @7
    @12
    @3
    @13
    @11
    @14
    @15
    @16
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
    cB
    cR
    cO
    cT
    vh
    @4
    cH
    cI
    cK
    c.le
    chlt
    cW
    @5
    cO
    dihjust.b
    dihjust.l
    dihjust.h
    dihord2c.t
    dihord2c.r
    dihord2c.o
    dihjust.i
    dibopelval3
    syl12anc
    mpbir2and
end
