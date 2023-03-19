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
include "wceq.mm"
include "simp1.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendospid.mm"
include "syl.mm"
include "eqcomd.mm"
include "tendoidcl.mm"
include "wb.mm"
include "cv.mm"
include "crio.mm"
include "cvv.mm"
include "riotaex.mm"
include "eqeltri.mm"
include "cltrn.mm"
include "fvex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "dicopelval2.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem cdlemn11a
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
  let vy: setvar y
  let vz: setvar z
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

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint N h
  disjoint P h
  disjoint Q h
  disjoint T h
  disjoint W h
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint s y
  disjoint s z
  disjoint .+ s
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .\/ g
  disjoint .\/ s
  disjoint .\/ y
  disjoint .\/ z
  disjoint g h
  disjoint .<_ g
  disjoint h s
  disjoint h y
  disjoint h z
  disjoint .<_ s
  disjoint .<_ y
  disjoint .<_ z
  disjoint A g
  disjoint A s
  disjoint A y
  disjoint A z
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint E g
  disjoint E s
  disjoint F g
  disjoint G g
  disjoint G s
  disjoint G y
  disjoint G z
  disjoint I g
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint .(+) g
  disjoint .(+) s
  disjoint .(+) y
  disjoint .(+) z
  disjoint H g
  disjoint H s
  disjoint H y
  disjoint H z
  disjoint K g
  disjoint K s
  disjoint K y
  disjoint K z
  disjoint N g
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint J g
  disjoint J s
  disjoint J y
  disjoint J z
  disjoint Q g
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint R s
  disjoint T g
  disjoint T s
  disjoint T y
  disjoint T z
  disjoint O g
  disjoint O s
  disjoint U y
  disjoint U z
  disjoint W g
  disjoint W s
  disjoint W y
  disjoint W z
  disjoint X g
  disjoint X s
  disjoint X y
  disjoint X z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ ( J ` N ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) ) -> <. G , ( _I |` T ) >. e. ( J ` N ) )

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
    cX
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cN
    cJ
    cfv
    #
    cQ
    cJ
    cfv
    cX
    cI
    cfv
    c.po
    co
    wss
    #
    w3a
    #
    cG
    cid
    cT
    cres
    #
    cop
    @5
    wcel
    #
    cG
    cG
    @8
    cfv
    #
    wceq
    #
    @8
    cE
    wcel
    #
    @7
    @10
    cG
    @7
    cG
    cT
    wcel
    #
    @10
    cG
    wceq
    @7
    @0
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
    @2
    @13
    @0
    @4
    @6
    simp1
    #
    @0
    @4
    @14
    @6
    cA
    cP
    cH
    cK
    c.le
    cW
    cdlemn11a.l
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.p
    lhpocnel2
    3ad2ant1
    @0
    @1
    @2
    @3
    @6
    simp22
    #
    cA
    cP
    cN
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    cdlemn11a.l
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.t
    cdlemn11a.g
    ltrniotacl
    syl3anc
    cT
    cG
    tendospid
    syl
    eqcomd
    @0
    @4
    @12
    @6
    cT
    cE
    cH
    cK
    cW
    cdlemn11a.h
    cdlemn11a.t
    cdlemn11a.e
    tendoidcl
    3ad2ant1
    @7
    @0
    @2
    @9
    @11
    @12
    wa
    wb
    @15
    @16
    cA
    cP
    cN
    @8
    cT
    vh
    cE
    cG
    cG
    cH
    cJ
    cK
    c.le
    chlt
    cW
    cdlemn11a.l
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.p
    cdlemn11a.t
    cdlemn11a.e
    cdlemn11a.J
    cdlemn11a.g
    cG
    cP
    vh
    cv
    cfv
    cN
    wceq
    #
    vh
    cT
    crio
    cvv
    cdlemn11a.g
    @17
    vh
    cT
    riotaex
    eqeltri
    cT
    cvv
    wcel
    @8
    cvv
    wcel
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    cdlemn11a.t
    cW
    @18
    fvex
    eqeltri
    cT
    cvv
    resiexg
    ax-mp
    dicopelval2
    syl2anc
    mpbir2and
end
