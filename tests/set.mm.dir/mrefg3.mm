include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wss.mm"
include "wb.mm"
include "mrefg2.mm"
include "adantr.mm"
include "simpll.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "adantl.mm"
include "simplr.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem mrefg3
  let cC: class C
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  assume isnacs.f: |- F = ( mrCls ` C )

  disjoint C g
  disjoint F g
  disjoint S g
  disjoint X g
  disjoint C c
  disjoint C s
  disjoint c g
  disjoint c s
  disjoint g s
  disjoint F c
  disjoint F s
  disjoint S s
  disjoint X c
  disjoint X s
  disjoint X x
  disjoint c x
  disjoint g x
  disjoint s x
  assert |- ( ( C e. ( Moore ` X ) /\ S e. C ) -> ( E. g e. ( ~P X i^i Fin ) S = ( F ` g ) <-> E. g e. ( ~P S i^i Fin ) S C_ ( F ` g ) ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cS
    cC
    wcel
    #
    wa
    #
    cS
    vg
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vg
    cX
    cpw
    cfn
    cin
    wrex
    #
    @5
    vg
    cS
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cS
    @4
    wss
    #
    vg
    @8
    wrex
    @0
    @6
    @9
    wb
    @1
    cC
    cS
    vg
    cF
    cX
    isnacs.f
    mrefg2
    adantr
    @2
    @5
    @10
    vg
    @8
    @2
    @3
    @8
    wcel
    #
    wa
    #
    @10
    @10
    @4
    cS
    wss
    #
    wa
    @5
    @12
    @13
    @10
    @12
    @0
    @3
    cS
    wss
    #
    @1
    @13
    @0
    @1
    @11
    simpll
    @11
    @14
    @2
    @11
    @3
    cS
    @8
    @7
    @3
    @7
    cfn
    inss1
    sseli
    elpwid
    adantl
    @0
    @1
    @11
    simplr
    cC
    @3
    cF
    cS
    cX
    isnacs.f
    mrcsscl
    syl3anc
    biantrud
    cS
    @4
    eqss
    syl6rbbr
    rexbidva
    bitrd
end
