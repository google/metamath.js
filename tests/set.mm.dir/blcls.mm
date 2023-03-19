include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "ccld.mm"
include "cbl.mm"
include "co.mm"
include "wss.mm"
include "ccl.mm"
include "blcld.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wral.mm"
include "blssm.mm"
include "clt.mm"
include "wa.mm"
include "elbl.mm"
include "wi.mm"
include "xmetcl.mm"
include "3expa.mm"
include "3adantl3.mm"
include "simpl3.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "expimpd.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "ssrab.mm"
include "sylanbrc.mm"
include "syl6sseqr.mm"
include "cuni.mm"
include "eqid.mm"
include "clsss2.mm"

theorem blcls
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vr: setvar r
  let vw: setvar w
  let cN: class N
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )
  assume blcld.3: |- S = { z e. X | ( P D z ) <_ R }

  disjoint D z
  disjoint R z
  disjoint P z
  disjoint X z
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint N r
  disjoint N y
  disjoint P r
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint T z
  disjoint X r
  disjoint X w
  disjoint X x
  disjoint X y
  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( ( cls ` J ) ` ( P ( ball ` D ) R ) ) C_ S )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    #
    cS
    cJ
    ccld
    cfv
    wcel
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cS
    wss
    @4
    cJ
    ccl
    cfv
    cfv
    cS
    wss
    vz
    cD
    cP
    cR
    cS
    cJ
    cX
    mopni.1
    blcld.3
    blcld
    @3
    @4
    cP
    vz
    cv
    #
    cD
    co
    #
    cR
    cle
    wbr
    #
    vz
    cX
    crab
    #
    cS
    @3
    @4
    cX
    wss
    @7
    vz
    @4
    wral
    @4
    @8
    wss
    cD
    cP
    cR
    cX
    blssm
    @3
    @7
    vz
    @4
    @3
    @5
    @4
    wcel
    @5
    cX
    wcel
    #
    @6
    cR
    clt
    wbr
    #
    wa
    @7
    @5
    cD
    cP
    cR
    cX
    elbl
    @3
    @9
    @10
    @7
    @3
    @9
    wa
    @6
    cxr
    wcel
    #
    @2
    @10
    @7
    wi
    @0
    @1
    @9
    @11
    @2
    @0
    @1
    @9
    @11
    cP
    @5
    cD
    cX
    xmetcl
    3expa
    3adantl3
    @0
    @1
    @2
    @9
    simpl3
    @6
    cR
    xrltle
    syl2anc
    expimpd
    sylbid
    ralrimiv
    @7
    vz
    cX
    @4
    ssrab
    sylanbrc
    blcld.3
    syl6sseqr
    cS
    @4
    cJ
    cJ
    cuni
    #
    @12
    eqid
    clsss2
    syl2anc
end
