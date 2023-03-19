include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cdlemn11b.mm"
include "csubg.mm"
include "wb.mm"
include "clss.mm"
include "clmod.mm"
include "simp1.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simp21.mm"
include "diclss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "simp23l.mm"
include "simp23r.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmelval.mm"
include "mpbid.mm"

theorem cdlemn11c
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
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  assume cdlemn11a.b: |- B = ( Base ` K )
  assume cdlemn11a.l: |- .<_ = ( le ` K )
  assume cdlemn11a.j: |- .\/ = ( join ` K )
  assume cdlemn11a.a: |- A = ( Atoms ` K )
  assume cdlemn11a.h: |- H = ( LHyp ` K )
  assume cdlemn11a.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn11a.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn11a.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn11a.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemn11a.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemn11a.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn11a.J: |- J = ( ( DIsoC ` K ) ` W )
  assume cdlemn11a.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn11a.d: |- .+ = ( +g ` U )
  assume cdlemn11a.s: |- .(+) = ( LSSum ` U )
  assume cdlemn11a.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn11a.g: |- G = ( iota_ h e. T ( h ` P ) = N )

  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .\/ y
  disjoint .\/ z
  disjoint h y
  disjoint h z
  disjoint .<_ h
  disjoint .<_ y
  disjoint .<_ z
  disjoint A h
  disjoint A y
  disjoint A z
  disjoint B h
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint I y
  disjoint I z
  disjoint .(+) y
  disjoint .(+) z
  disjoint H h
  disjoint H y
  disjoint H z
  disjoint K h
  disjoint K y
  disjoint K z
  disjoint N h
  disjoint N y
  disjoint N z
  disjoint J y
  disjoint J z
  disjoint P h
  disjoint Q h
  disjoint Q y
  disjoint Q z
  disjoint T h
  disjoint T y
  disjoint T z
  disjoint U y
  disjoint U z
  disjoint W h
  disjoint W y
  disjoint W z
  disjoint X y
  disjoint X z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint s y
  disjoint s z
  disjoint .+ s
  disjoint .\/ g
  disjoint .\/ s
  disjoint g h
  disjoint .<_ g
  disjoint h s
  disjoint .<_ s
  disjoint A g
  disjoint A s
  disjoint B g
  disjoint B s
  disjoint E g
  disjoint E s
  disjoint F g
  disjoint G g
  disjoint G s
  disjoint I g
  disjoint I s
  disjoint .(+) g
  disjoint .(+) s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint K s
  disjoint N g
  disjoint N s
  disjoint J g
  disjoint J s
  disjoint Q g
  disjoint Q s
  disjoint R s
  disjoint T g
  disjoint T s
  disjoint O g
  disjoint O s
  disjoint W g
  disjoint W s
  disjoint X g
  disjoint X s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ ( J ` N ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) ) -> E. y e. ( J ` Q ) E. z e. ( I ` X ) <. G , ( _I |` T ) >. = ( y .+ z ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cN
    cJ
    cfv
    cQ
    cJ
    cfv
    #
    cX
    cI
    cfv
    #
    c.po
    co
    #
    wss
    #
    w3a
    #
    cG
    cid
    cT
    cres
    cop
    #
    @9
    wcel
    #
    @12
    vy
    cv
    vz
    cv
    c.pl
    co
    wceq
    vz
    @8
    wrex
    vy
    @7
    wrex
    #
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
    cF
    cG
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cN
    cO
    cW
    cX
    cdlemn11a.b
    cdlemn11a.l
    cdlemn11a.j
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.p
    cdlemn11a.o
    cdlemn11a.t
    cdlemn11a.r
    cdlemn11a.e
    cdlemn11a.i
    cdlemn11a.J
    cdlemn11a.u
    cdlemn11a.d
    cdlemn11a.s
    cdlemn11a.f
    cdlemn11a.g
    cdlemn11b
    @11
    @7
    cU
    csubg
    cfv
    #
    wcel
    @8
    @15
    wcel
    @13
    @14
    wb
    @11
    cU
    clss
    cfv
    #
    @15
    @7
    @11
    cU
    clmod
    wcel
    @16
    @15
    wss
    @11
    cU
    cH
    cK
    cW
    cdlemn11a.h
    cdlemn11a.u
    @0
    @6
    @10
    simp1
    #
    dvhlmod
    @16
    cU
    @16
    eqid
    #
    lsssssubg
    syl
    #
    @11
    @0
    @1
    @7
    @16
    wcel
    @17
    @0
    @1
    @2
    @5
    @10
    simp21
    cA
    cQ
    @16
    cU
    cH
    cJ
    cK
    c.le
    cW
    cdlemn11a.l
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.u
    cdlemn11a.J
    @18
    diclss
    syl2anc
    sseldd
    @11
    @16
    @15
    @8
    @19
    @11
    @0
    @3
    @4
    @8
    @16
    wcel
    @17
    @3
    @4
    @1
    @2
    @0
    @10
    simp23l
    @3
    @4
    @1
    @2
    @0
    @10
    simp23r
    cB
    @16
    cU
    cH
    cI
    cK
    c.le
    cW
    cX
    cdlemn11a.b
    cdlemn11a.l
    cdlemn11a.h
    cdlemn11a.u
    cdlemn11a.i
    @18
    diblss
    syl12anc
    sseldd
    vy
    vz
    c.pl
    c.po
    @7
    @8
    cU
    @12
    cdlemn11a.d
    cdlemn11a.s
    lsmelval
    syl2anc
    mpbid
end
