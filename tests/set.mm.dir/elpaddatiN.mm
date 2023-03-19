include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "elpaddat.mm"
include "simpr.mm"
include "syl6bi.mm"
include "impr.mm"

theorem elpaddatiN
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
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
  let cS: class S
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint A p
  disjoint K p
  disjoint X p
  disjoint .\/ p
  disjoint .<_ p
  disjoint Q p
  disjoint R p
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
  disjoint S p
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
  assert |- ( ( ( K e. Lat /\ X C_ A /\ Q e. A ) /\ ( X =/= (/) /\ R e. ( X .+ { Q } ) ) ) -> E. p e. X R .<_ ( p .\/ Q ) )

  proof
    cK
    clat
    wcel
    cX
    cA
    wss
    cQ
    cA
    wcel
    w3a
    #
    cX
    c0
    wne
    #
    cR
    cX
    cQ
    csn
    c.pl
    co
    wcel
    #
    cR
    vp
    cv
    cQ
    c.or
    co
    c.le
    wbr
    vp
    cX
    wrex
    #
    @0
    @1
    wa
    @2
    cR
    cA
    wcel
    #
    @3
    wa
    @3
    cA
    c.pl
    cQ
    cR
    c.or
    cK
    c.le
    cX
    vp
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpaddat
    @4
    @3
    simpr
    syl6bi
    impr
end
