include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cword.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wral.mm"
include "cs1.mm"
include "cconcat.mm"
include "ccom.mm"
include "simpr.mm"
include "anim12i.mm"
include "3adant3.mm"
include "adantl.mm"
include "adantr.mm"
include "simpll3.mm"
include "simprl.mm"
include "3jca.mm"
include "fvcosymgeq.mm"
include "sylc.mm"
include "simpl1.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "gsumccatsymgsn.mm"
include "syl.mm"
include "fveq1d.mm"
include "simpl2.mm"
include "simpr2l.mm"
include "simpr2r.mm"
include "3eqtr4d.mm"
include "ex.mm"

theorem gsmsymgreqlem1
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vi: setvar i
  let cK: class K
  let cW: class W
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cH: class H
  assume gsmsymgrfix.s: |- S = ( SymGrp ` N )
  assume gsmsymgrfix.b: |- B = ( Base ` S )
  assume gsmsymgreq.z: |- Z = ( SymGrp ` M )
  assume gsmsymgreq.p: |- P = ( Base ` Z )
  assume gsmsymgreq.i: |- I = ( N i^i M )

  disjoint I n
  disjoint X n
  disjoint C n
  disjoint J n
  disjoint R n
  disjoint S n
  disjoint Y n
  disjoint Z n
  disjoint B i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint W i
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint W w
  disjoint F n
  disjoint G n
  disjoint H n
  disjoint K n
  assert |- ( ( ( N e. Fin /\ M e. Fin /\ J e. I ) /\ ( ( X e. Word B /\ C e. B ) /\ ( Y e. Word P /\ R e. P ) /\ ( # ` X ) = ( # ` Y ) ) ) -> ( ( A. n e. I ( ( S gsum X ) ` n ) = ( ( Z gsum Y ) ` n ) /\ ( C ` J ) = ( R ` J ) ) -> ( ( S gsum ( X ++ <" C "> ) ) ` J ) = ( ( Z gsum ( Y ++ <" R "> ) ) ` J ) ) )

  proof
    cN
    cfn
    wcel
    #
    cM
    cfn
    wcel
    #
    cJ
    cI
    wcel
    #
    w3a
    #
    cX
    cB
    cword
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cY
    cP
    cword
    wcel
    #
    cR
    cP
    wcel
    #
    wa
    #
    cX
    chash
    cfv
    cY
    chash
    cfv
    wceq
    #
    w3a
    #
    wa
    #
    vn
    cv
    #
    cS
    cX
    cgsu
    co
    #
    cfv
    @13
    cZ
    cY
    cgsu
    co
    #
    cfv
    wceq
    vn
    cI
    wral
    #
    cJ
    cC
    cfv
    cJ
    cR
    cfv
    wceq
    #
    wa
    #
    cJ
    cS
    cX
    cC
    cs1
    cconcat
    co
    cgsu
    co
    #
    cfv
    #
    cJ
    cZ
    cY
    cR
    cs1
    cconcat
    co
    cgsu
    co
    #
    cfv
    #
    wceq
    @12
    @18
    wa
    #
    cJ
    @14
    cC
    ccom
    #
    cfv
    #
    cJ
    @15
    cR
    ccom
    #
    cfv
    #
    @20
    @22
    @23
    @5
    @8
    wa
    #
    @2
    @17
    @16
    w3a
    @25
    @27
    wceq
    @12
    @28
    @18
    @11
    @28
    @3
    @6
    @9
    @28
    @10
    @6
    @5
    @9
    @8
    @4
    @5
    simpr
    @7
    @8
    simpr
    anim12i
    3adant3
    adantl
    adantr
    @23
    @2
    @17
    @16
    @0
    @1
    @2
    @11
    @18
    simpll3
    @18
    @17
    @12
    @16
    @17
    simpr
    adantl
    @12
    @16
    @17
    simprl
    3jca
    cB
    cP
    cS
    vn
    @14
    cC
    @15
    cI
    cR
    cM
    cN
    cJ
    cZ
    gsmsymgrfix.s
    gsmsymgrfix.b
    gsmsymgreq.z
    gsmsymgreq.p
    gsmsymgreq.i
    fvcosymgeq
    sylc
    @23
    cJ
    @19
    @24
    @23
    @0
    @4
    @5
    w3a
    #
    @19
    @24
    wceq
    @12
    @29
    @18
    @12
    @0
    @4
    @5
    @0
    @1
    @2
    @11
    simpl1
    @4
    @5
    @9
    @10
    @3
    simpr1l
    @4
    @5
    @9
    @10
    @3
    simpr1r
    3jca
    adantr
    cN
    cB
    cS
    cfn
    cX
    cC
    gsmsymgrfix.s
    gsmsymgrfix.b
    gsumccatsymgsn
    syl
    fveq1d
    @23
    cJ
    @21
    @26
    @23
    @1
    @7
    @8
    w3a
    #
    @21
    @26
    wceq
    @12
    @30
    @18
    @12
    @1
    @7
    @8
    @0
    @1
    @2
    @11
    simpl2
    @7
    @8
    @6
    @10
    @3
    simpr2l
    @7
    @8
    @6
    @10
    @3
    simpr2r
    3jca
    adantr
    cM
    cP
    cZ
    cfn
    cY
    cR
    gsmsymgreq.z
    gsmsymgreq.p
    gsumccatsymgsn
    syl
    fveq1d
    3eqtr4d
    ex
end
