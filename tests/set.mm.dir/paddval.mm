include "wcel.mm"
include "wss.mm"
include "cpw.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wceq.mm"
include "biid.mm"
include "catm.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "w3a.mm"
include "cmpt2.mm"
include "paddfval.mm"
include "oveqd.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "unexg.mm"
include "rabex.mm"
include "sylancl.mm"
include "3jca.mm"
include "3adant1.mm"
include "uneq1.mm"
include "rexeq.mm"
include "rabbidv.mm"
include "uneq12d.mm"
include "uneq2.mm"
include "rexbidv.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "syl.mm"
include "eqtrd.mm"
include "syl3anbr.mm"

theorem paddval
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint A p
  disjoint p q
  disjoint p r
  disjoint K p
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint X p
  disjoint X q
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint h m
  disjoint h n
  disjoint h p
  disjoint h s
  disjoint A h
  disjoint m n
  disjoint m p
  disjoint m s
  disjoint A m
  disjoint n p
  disjoint n s
  disjoint A n
  disjoint p s
  disjoint A s
  disjoint .\/ h
  disjoint h q
  disjoint h r
  disjoint K h
  disjoint m q
  disjoint m r
  disjoint K m
  disjoint n q
  disjoint n r
  disjoint K n
  disjoint q s
  disjoint r s
  disjoint K s
  disjoint .<_ h
  disjoint .\/ m
  disjoint .\/ n
  disjoint .\/ s
  disjoint .<_ m
  disjoint .<_ n
  disjoint .<_ s
  disjoint X m
  disjoint X n
  disjoint X s
  disjoint Y m
  disjoint Y n
  disjoint Y s
  assert |- ( ( K e. B /\ X C_ A /\ Y C_ A ) -> ( X .+ Y ) = ( ( X u. Y ) u. { p e. A | E. q e. X E. r e. Y p .<_ ( q .\/ r ) } ) )

  proof
    cK
    cB
    wcel
    #
    @0
    cX
    cA
    wss
    cX
    cA
    cpw
    #
    wcel
    #
    cY
    cA
    wss
    cY
    @1
    wcel
    #
    cX
    cY
    c.pl
    co
    #
    cX
    cY
    cun
    #
    vp
    cv
    vq
    cv
    vr
    cv
    c.or
    co
    c.le
    wbr
    #
    vr
    cY
    wrex
    #
    vq
    cX
    wrex
    #
    vp
    cA
    crab
    #
    cun
    #
    wceq
    @0
    biid
    cX
    cA
    cA
    cK
    catm
    cfv
    cvv
    paddfval.a
    cK
    catm
    fvex
    eqeltri
    #
    elpw2
    cY
    cA
    @11
    elpw2
    @0
    @2
    @3
    w3a
    #
    @4
    cX
    cY
    vm
    vn
    @1
    @1
    vm
    cv
    #
    vn
    cv
    #
    cun
    #
    @6
    vr
    @14
    wrex
    #
    vq
    @13
    wrex
    #
    vp
    cA
    crab
    #
    cun
    #
    cmpt2
    #
    co
    #
    @10
    @0
    @2
    @4
    @21
    wceq
    @3
    @0
    c.pl
    @20
    cX
    cY
    cA
    cB
    c.pl
    vm
    vn
    c.or
    cK
    c.le
    vr
    vq
    vp
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    paddfval
    oveqd
    3ad2ant1
    @12
    @2
    @3
    @10
    cvv
    wcel
    #
    w3a
    #
    @21
    @10
    wceq
    @2
    @3
    @23
    @0
    @2
    @3
    wa
    #
    @2
    @3
    @22
    @2
    @3
    simpl
    @2
    @3
    simpr
    @24
    @5
    cvv
    wcel
    @9
    cvv
    wcel
    @22
    cX
    cY
    @1
    @1
    unexg
    @8
    vp
    cA
    @11
    rabex
    @5
    @9
    cvv
    cvv
    unexg
    sylancl
    3jca
    3adant1
    vm
    vn
    cX
    cY
    @1
    @1
    @19
    @10
    @20
    cX
    @14
    cun
    #
    @16
    vq
    cX
    wrex
    #
    vp
    cA
    crab
    #
    cun
    cvv
    @13
    cX
    wceq
    #
    @15
    @25
    @18
    @27
    @13
    cX
    @14
    uneq1
    @28
    @17
    @26
    vp
    cA
    @16
    vq
    @13
    cX
    rexeq
    rabbidv
    uneq12d
    @14
    cY
    wceq
    #
    @25
    @5
    @27
    @9
    @14
    cY
    cX
    uneq2
    @29
    @26
    @8
    vp
    cA
    @29
    @16
    @7
    vq
    cX
    @6
    vr
    @14
    cY
    rexeq
    rexbidv
    rabbidv
    uneq12d
    @20
    eqid
    ovmpt2g
    syl
    eqtrd
    syl3anbr
end
