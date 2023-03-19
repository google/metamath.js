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
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "dihord11b.mm"
include "syl32anc.mm"
include "csubg.mm"
include "wb.mm"
include "clss.mm"
include "clmod.mm"
include "simp11.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simp13.mm"
include "diclss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "simp2r.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmelval.mm"
include "mpbid.mm"

theorem dihord11c
  let vy: setvar y
  let vz: setvar z
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

  disjoint f y
  disjoint f z
  disjoint .\/ f
  disjoint y z
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ f
  disjoint ./\ y
  disjoint ./\ z
  disjoint .(+) f
  disjoint .(+) y
  disjoint .(+) z
  disjoint .+ y
  disjoint .+ z
  disjoint f h
  disjoint A f
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint A y
  disjoint A z
  disjoint I f
  disjoint I y
  disjoint I z
  disjoint J f
  disjoint J y
  disjoint J z
  disjoint O y
  disjoint O z
  disjoint P h
  disjoint Q f
  disjoint Q y
  disjoint Q z
  disjoint R f
  disjoint R y
  disjoint R z
  disjoint B f
  disjoint B h
  disjoint B y
  disjoint B z
  disjoint H f
  disjoint H h
  disjoint H y
  disjoint H z
  disjoint K f
  disjoint K h
  disjoint K y
  disjoint K z
  disjoint U y
  disjoint U z
  disjoint .<_ f
  disjoint .<_ h
  disjoint .<_ y
  disjoint .<_ z
  disjoint N f
  disjoint N h
  disjoint N y
  disjoint N z
  disjoint T f
  disjoint T h
  disjoint T y
  disjoint T z
  disjoint W f
  disjoint W h
  disjoint W y
  disjoint W z
  disjoint X f
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y y
  disjoint Y z
  disjoint f g
  disjoint f s
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint .\/ g
  disjoint s y
  disjoint s z
  disjoint .\/ s
  disjoint ./\ g
  disjoint ./\ s
  disjoint .(+) g
  disjoint .(+) s
  disjoint E g
  disjoint E s
  disjoint .+ g
  disjoint .+ s
  disjoint g h
  disjoint A g
  disjoint h s
  disjoint A s
  disjoint I g
  disjoint I s
  disjoint J g
  disjoint J s
  disjoint G g
  disjoint O g
  disjoint O s
  disjoint Q g
  disjoint Q s
  disjoint R g
  disjoint R s
  disjoint B g
  disjoint B s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint K s
  disjoint .<_ g
  disjoint .<_ s
  disjoint N g
  disjoint N s
  disjoint T g
  disjoint T s
  disjoint W g
  disjoint W s
  disjoint X g
  disjoint X s
  disjoint Y g
  disjoint Y s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` N ) .(+) ( I ` ( Y ./\ W ) ) ) /\ f e. T /\ ( R ` f ) .<_ ( X ./\ W ) ) ) -> E. y e. ( J ` N ) E. z e. ( I ` ( Y ./\ W ) ) <. f , O >. = ( y .+ z ) )

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
    c.po
    co
    cN
    cJ
    cfv
    #
    cY
    cW
    c.an
    co
    #
    cI
    cfv
    #
    c.po
    co
    #
    wss
    #
    vf
    cv
    #
    cT
    wcel
    #
    @15
    cR
    cfv
    @9
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    @15
    cO
    cop
    #
    @13
    wcel
    #
    @20
    vy
    cv
    vz
    cv
    c.pl
    co
    wceq
    vz
    @12
    wrex
    vy
    @10
    wrex
    #
    @19
    @5
    @8
    @14
    @16
    @17
    @21
    @5
    @8
    @18
    simp1
    @5
    @8
    @18
    simp2
    @5
    @8
    @14
    @16
    @17
    simp31
    @5
    @8
    @14
    @16
    @17
    simp32
    @5
    @8
    @14
    @16
    @17
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
    vf
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
    dihord11b
    syl32anc
    @19
    @10
    cU
    csubg
    cfv
    #
    wcel
    @12
    @23
    wcel
    @21
    @22
    wb
    @19
    cU
    clss
    cfv
    #
    @23
    @10
    @19
    cU
    clmod
    wcel
    @24
    @23
    wss
    @19
    cU
    cH
    cK
    cW
    dihjust.h
    dihjust.u
    @2
    @3
    @4
    @8
    @18
    simp11
    #
    dvhlmod
    @24
    cU
    @24
    eqid
    #
    lsssssubg
    syl
    #
    @19
    @2
    @4
    @10
    @24
    wcel
    @25
    @2
    @3
    @4
    @8
    @18
    simp13
    cA
    cN
    @24
    cU
    cH
    cJ
    cK
    c.le
    cW
    dihjust.l
    dihjust.a
    dihjust.h
    dihjust.u
    dihjust.J
    @26
    diclss
    syl2anc
    sseldd
    @19
    @24
    @23
    @12
    @27
    @19
    @2
    @11
    cB
    wcel
    #
    @11
    cW
    c.le
    wbr
    #
    @12
    @24
    wcel
    @25
    @19
    cK
    clat
    wcel
    #
    @7
    cW
    cB
    wcel
    #
    @28
    @19
    @0
    @30
    @0
    @1
    @3
    @4
    @8
    @18
    simp11l
    cK
    hllat
    syl
    #
    @5
    @6
    @7
    @18
    simp2r
    #
    @19
    @1
    @31
    @0
    @1
    @3
    @4
    @8
    @18
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
    cY
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    @19
    @30
    @7
    @31
    @29
    @32
    @33
    @34
    cB
    cK
    c.le
    c.an
    cY
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
    cB
    @24
    cU
    cH
    cI
    cK
    c.le
    cW
    @11
    dihjust.b
    dihjust.l
    dihjust.h
    dihjust.u
    dihjust.i
    @26
    diblss
    syl12anc
    sseldd
    vy
    vz
    c.pl
    c.po
    @10
    @12
    cU
    @20
    dihord2.d
    dihjust.s
    lsmelval
    syl2anc
    mpbid
end
