include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "ccld.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "ccl.mm"
include "wi.mm"
include "sstr2.mm"
include "adantr.mm"
include "ss2rabdv.mm"
include "intss.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "wceq.mm"
include "simp1.mm"
include "impcom.mm"
include "3adant1.mm"
include "clsval.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3sstr4d.mm"

theorem clsss
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X /\ T C_ S ) -> ( ( cls ` J ) ` T ) C_ ( ( cls ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cT
    cS
    wss
    #
    w3a
    #
    cT
    vx
    cv
    #
    wss
    #
    vx
    cJ
    ccld
    cfv
    #
    crab
    #
    cint
    #
    cS
    @4
    wss
    #
    vx
    @6
    crab
    #
    cint
    #
    cT
    cJ
    ccl
    cfv
    #
    cfv
    #
    cS
    @12
    cfv
    #
    @2
    @0
    @8
    @11
    wss
    #
    @1
    @2
    @10
    @7
    wss
    @15
    @2
    @9
    @5
    vx
    @6
    @2
    @9
    @5
    wi
    @4
    @6
    wcel
    cT
    cS
    @4
    sstr2
    adantr
    ss2rabdv
    @10
    @7
    intss
    syl
    3ad2ant3
    @3
    @0
    cT
    cX
    wss
    #
    @13
    @8
    wceq
    @0
    @1
    @2
    simp1
    @1
    @2
    @16
    @0
    @2
    @1
    @16
    cT
    cS
    cX
    sstr2
    impcom
    3adant1
    vx
    cT
    cJ
    cX
    clscld.1
    clsval
    syl2anc
    @0
    @1
    @14
    @11
    wceq
    @2
    vx
    cS
    cJ
    cX
    clscld.1
    clsval
    3adant3
    3sstr4d
end
