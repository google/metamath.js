include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wceq.mm"
include "metss.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "eqss.mm"
include "r19.26.mm"
include "3bitr4g.mm"

theorem metequiv
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let wph: wff ph
  assume metequiv.3: |- J = ( MetOpen ` C )
  assume metequiv.4: |- K = ( MetOpen ` D )

  disjoint r s
  disjoint r x
  disjoint C r
  disjoint s x
  disjoint C s
  disjoint C x
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint K r
  disjoint K s
  disjoint K x
  disjoint D r
  disjoint D s
  disjoint D x
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint a b
  disjoint a x
  disjoint C a
  disjoint b x
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  disjoint X a
  disjoint X b
  disjoint r y
  disjoint r z
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J y
  disjoint K y
  disjoint R s
  disjoint R y
  disjoint S y
  disjoint D y
  disjoint D z
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint X y
  disjoint X z
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` X ) ) -> ( J = K <-> A. x e. X ( A. r e. RR+ E. s e. RR+ ( x ( ball ` D ) s ) C_ ( x ( ball ` C ) r ) /\ A. a e. RR+ E. b e. RR+ ( x ( ball ` C ) b ) C_ ( x ( ball ` D ) a ) ) ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
    cJ
    cK
    wss
    #
    cK
    cJ
    wss
    #
    wa
    vx
    cv
    #
    vs
    cv
    cD
    cbl
    cfv
    #
    co
    @6
    vr
    cv
    cC
    cbl
    cfv
    #
    co
    wss
    vs
    crp
    wrex
    vr
    crp
    wral
    #
    vx
    cX
    wral
    #
    @6
    vb
    cv
    @8
    co
    @6
    va
    cv
    @7
    co
    wss
    vb
    crp
    wrex
    va
    crp
    wral
    #
    vx
    cX
    wral
    #
    wa
    cJ
    cK
    wceq
    @9
    @11
    wa
    vx
    cX
    wral
    @3
    @4
    @10
    @5
    @12
    vx
    cC
    cD
    cJ
    cK
    cX
    vs
    vr
    metequiv.3
    metequiv.4
    metss
    @2
    @1
    @5
    @12
    wb
    vx
    cD
    cC
    cK
    cJ
    cX
    vb
    va
    metequiv.4
    metequiv.3
    metss
    ancoms
    anbi12d
    cJ
    cK
    eqss
    @9
    @11
    vx
    cX
    r19.26
    3bitr4g
end
