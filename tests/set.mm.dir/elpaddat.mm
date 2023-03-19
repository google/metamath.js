include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "snssd.mm"
include "simpr.mm"
include "snnzg.mm"
include "syl.mm"
include "elpaddn0.mm"
include "syl32anc.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rexsng.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem elpaddat
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vp: setvar p
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vq: setvar q
  let vr: setvar r
  let cY: class Y
  let cR: class R
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint A p
  disjoint K p
  disjoint X p
  disjoint .\/ p
  disjoint .<_ p
  disjoint S p
  disjoint Q p
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
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint q s
  disjoint K q
  disjoint r s
  disjoint K r
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
  disjoint X q
  disjoint X s
  disjoint Y m
  disjoint Y n
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint Y s
  disjoint S q
  disjoint S r
  disjoint A q
  disjoint A r
  disjoint .\/ q
  disjoint .\/ r
  disjoint .<_ q
  disjoint .<_ r
  disjoint .+ s
  disjoint X r
  disjoint Q q
  disjoint Q r
  disjoint R r
  assert |- ( ( ( K e. Lat /\ X C_ A /\ Q e. A ) /\ X =/= (/) ) -> ( S e. ( X .+ { Q } ) <-> ( S e. A /\ E. p e. X S .<_ ( p .\/ Q ) ) ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cA
    wss
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cX
    c0
    wne
    #
    wa
    #
    cS
    cX
    cQ
    csn
    #
    c.pl
    co
    wcel
    #
    cS
    cA
    wcel
    #
    cS
    vp
    cv
    #
    vr
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    @6
    wrex
    #
    vp
    cX
    wrex
    #
    wa
    #
    @8
    cS
    @9
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    vp
    cX
    wrex
    #
    wa
    @5
    @0
    @1
    @6
    cA
    wss
    @4
    @6
    c0
    wne
    #
    @7
    @15
    wb
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    @5
    cQ
    cA
    @0
    @1
    @2
    @4
    simpl3
    #
    snssd
    @3
    @4
    simpr
    @5
    @2
    @19
    @20
    cQ
    cA
    snnzg
    syl
    cA
    c.pl
    cS
    c.or
    cK
    c.le
    cX
    @6
    vr
    vp
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpaddn0
    syl32anc
    @5
    @14
    @18
    @8
    @5
    @13
    @17
    vp
    cX
    @5
    @2
    @13
    @17
    wb
    @20
    @12
    @17
    vr
    cQ
    cA
    @10
    cQ
    wceq
    @11
    @16
    cS
    c.le
    @10
    cQ
    @9
    c.or
    oveq2
    breq2d
    rexsng
    syl
    rexbidv
    anbi2d
    bitrd
end
