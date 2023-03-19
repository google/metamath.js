include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "dihord2b.mm"
include "adantr.mm"
include "wceq.mm"
include "simpr.mm"
include "eqidd.mm"
include "wb.mm"
include "simpl11.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "dibopelval3.mm"
include "syl12anc.mm"
include "mpbir2and.mm"
include "sseldd.mm"

theorem dihord11b
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
  let vg: setvar g
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

  disjoint .\/ f
  disjoint ./\ f
  disjoint .(+) f
  disjoint f h
  disjoint A f
  disjoint A h
  disjoint I f
  disjoint J f
  disjoint P h
  disjoint Q f
  disjoint R f
  disjoint B f
  disjoint B h
  disjoint H f
  disjoint H h
  disjoint K f
  disjoint K h
  disjoint .<_ f
  disjoint .<_ h
  disjoint N f
  disjoint N h
  disjoint T f
  disjoint T h
  disjoint W f
  disjoint W h
  disjoint X f
  disjoint Y f
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
  disjoint N g
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
  disjoint Y g
  disjoint Y s
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` N ) .(+) ( I ` ( Y ./\ W ) ) ) ) /\ ( f e. T /\ ( R ` f ) .<_ ( X ./\ W ) ) ) -> <. f , O >. e. ( ( J ` N ) .(+) ( I ` ( Y ./\ W ) ) ) )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cQ
    cJ
    cfv
    cX
    cW
    c.an
    co
    #
    cI
    cfv
    #
    c.po
    co
    cN
    cJ
    cfv
    cY
    cW
    c.an
    co
    cI
    cfv
    c.po
    co
    #
    wss
    #
    w3a
    #
    vf
    cv
    #
    cT
    wcel
    @14
    cR
    cfv
    @9
    c.le
    wbr
    wa
    #
    wa
    #
    @10
    @11
    @14
    cO
    cop
    #
    @13
    @10
    @11
    wss
    @15
    cA
    cB
    c.po
    cQ
    cN
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.m
    dihjust.a
    dihjust.h
    dihjust.i
    dihjust.J
    dihjust.u
    dihjust.s
    dihord2b
    adantr
    @16
    @17
    @10
    wcel
    #
    @15
    cO
    cO
    wceq
    #
    @13
    @15
    simpr
    @16
    cO
    eqidd
    @16
    @2
    @9
    cB
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    @18
    @15
    @19
    wa
    wb
    @2
    @3
    @4
    @8
    @12
    @15
    simpl11
    @16
    cK
    clat
    wcel
    #
    @6
    cW
    cB
    wcel
    #
    @20
    @16
    @0
    @22
    @13
    @0
    @15
    @0
    @1
    @3
    @4
    @8
    @12
    simp11l
    adantr
    cK
    hllat
    syl
    #
    @6
    @7
    @5
    @12
    @15
    simpl2l
    #
    @16
    @1
    @23
    @13
    @1
    @15
    @0
    @1
    @3
    @4
    @8
    @12
    simp11r
    adantr
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
    @16
    @22
    @6
    @23
    @21
    @24
    @25
    @26
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
    @14
    cH
    cI
    cK
    c.le
    chlt
    cW
    @9
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
    sseldd
end
