include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "dihord2a.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "simp13l.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp33.mm"
include "dihord2pre.mm"
include "syld3an3.mm"
include "latlej2.mm"
include "lattrd.mm"
include "wb.mm"
include "simp12l.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"

theorem dihord2pre2
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
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
  let vf: setvar f
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

  disjoint A h
  disjoint P h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint .<_ h
  disjoint N h
  disjoint T h
  disjoint W h
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint f z
  disjoint .\/ f
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
  disjoint ./\ f
  disjoint ./\ g
  disjoint ./\ s
  disjoint ./\ y
  disjoint ./\ z
  disjoint .(+) f
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
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint h s
  disjoint h y
  disjoint h z
  disjoint A s
  disjoint A y
  disjoint A z
  disjoint I f
  disjoint I g
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint J f
  disjoint J g
  disjoint J s
  disjoint J y
  disjoint J z
  disjoint G g
  disjoint O g
  disjoint O s
  disjoint O y
  disjoint O z
  disjoint Q f
  disjoint Q g
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint R f
  disjoint R g
  disjoint R s
  disjoint R y
  disjoint R z
  disjoint B f
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint H f
  disjoint H g
  disjoint H s
  disjoint H y
  disjoint H z
  disjoint K f
  disjoint K g
  disjoint K s
  disjoint K y
  disjoint K z
  disjoint U y
  disjoint U z
  disjoint .<_ f
  disjoint .<_ g
  disjoint .<_ s
  disjoint .<_ y
  disjoint .<_ z
  disjoint N f
  disjoint N g
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint T f
  disjoint T g
  disjoint T s
  disjoint T y
  disjoint T z
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint W y
  disjoint W z
  disjoint X f
  disjoint X g
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y s
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( Q .\/ ( X ./\ W ) ) = X /\ ( N .\/ ( Y ./\ W ) ) = Y /\ ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` N ) .(+) ( I ` ( Y ./\ W ) ) ) ) ) -> ( Q .\/ ( X ./\ W ) ) .<_ ( N .\/ ( Y ./\ W ) ) )

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
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cN
    cA
    wcel
    #
    cN
    cW
    c.le
    wbr
    wn
    #
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
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    cN
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cY
    wceq
    #
    cQ
    cJ
    cfv
    @13
    cI
    cfv
    c.po
    co
    cN
    cJ
    cfv
    @16
    cI
    cfv
    c.po
    co
    wss
    #
    w3a
    #
    w3a
    #
    cQ
    @17
    c.le
    wbr
    #
    @13
    @17
    c.le
    wbr
    #
    @14
    @17
    c.le
    wbr
    #
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
    dihord2a
    @21
    cB
    cK
    c.le
    @13
    @16
    @17
    dihjust.b
    dihjust.l
    @21
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @12
    @20
    simp11l
    cK
    hllat
    syl
    #
    @21
    @25
    @10
    cW
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @26
    @9
    @10
    @11
    @20
    simp2l
    @21
    @1
    @27
    @0
    @1
    @5
    @8
    @12
    @20
    simp11r
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
    #
    @21
    @25
    @11
    @27
    @16
    cB
    wcel
    #
    @26
    @9
    @10
    @11
    @20
    simp2r
    @29
    cB
    cK
    c.an
    cY
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    #
    @21
    @25
    cN
    cB
    wcel
    #
    @31
    @17
    cB
    wcel
    #
    @26
    @21
    @6
    @33
    @6
    @7
    @2
    @5
    @12
    @20
    simp13l
    cA
    cB
    cN
    cK
    dihjust.b
    dihjust.a
    atbase
    syl
    #
    @32
    cB
    c.or
    cK
    cN
    @16
    dihjust.b
    dihjust.j
    latjcl
    syl3anc
    #
    @9
    @12
    @20
    @19
    @13
    @16
    c.le
    wbr
    @9
    @12
    @15
    @18
    @19
    simp33
    cA
    cB
    cP
    c.pl
    c.po
    cQ
    cR
    cT
    cU
    vh
    cE
    cG
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cN
    cO
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
    dihord2c.t
    dihord2c.r
    dihord2c.o
    dihord2.p
    dihord2.e
    dihord2.d
    dihord2.g
    dihord2pre
    syld3an3
    @21
    @25
    @33
    @31
    @16
    @17
    c.le
    wbr
    @26
    @35
    @32
    cB
    c.or
    cK
    c.le
    cN
    @16
    dihjust.b
    dihjust.l
    dihjust.j
    latlej2
    syl3anc
    lattrd
    @21
    @25
    cQ
    cB
    wcel
    #
    @28
    @34
    @22
    @23
    wa
    @24
    wb
    @26
    @21
    @3
    @37
    @3
    @4
    @2
    @8
    @12
    @20
    simp12l
    cA
    cB
    cQ
    cK
    dihjust.b
    dihjust.a
    atbase
    syl
    @30
    @36
    cB
    c.or
    cK
    c.le
    cQ
    @13
    @17
    dihjust.b
    dihjust.l
    dihjust.j
    latjle12
    syl13anc
    mpbi2and
end
