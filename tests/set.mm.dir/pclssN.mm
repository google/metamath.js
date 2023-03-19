include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cpsubsp.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "sstr2.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "ss2rabdv.mm"
include "intss.mm"
include "syl.mm"
include "wceq.mm"
include "simp1.mm"
include "sstr.mm"
include "3adant1.mm"
include "eqid.mm"
include "pclvalN.mm"
include "syl2anc.mm"
include "3adant2.mm"
include "3sstr4d.mm"

theorem pclssN
  let cA: class A
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume pclss.a: |- A = ( Atoms ` K )
  assume pclss.c: |- U = ( PCl ` K )


  assert |- ( ( K e. V /\ X C_ Y /\ Y C_ A ) -> ( U ` X ) C_ ( U ` Y ) )

  proof
    cK
    cV
    wcel
    #
    cX
    cY
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cX
    vy
    cv
    #
    wss
    #
    vy
    cK
    cpsubsp
    cfv
    #
    crab
    #
    cint
    #
    cY
    @4
    wss
    #
    vy
    @6
    crab
    #
    cint
    #
    cX
    cU
    cfv
    #
    cY
    cU
    cfv
    #
    @3
    @10
    @7
    wss
    @8
    @11
    wss
    @3
    @9
    @5
    vy
    @6
    @3
    @9
    @5
    wi
    #
    @4
    @6
    wcel
    @1
    @0
    @14
    @2
    cX
    cY
    @4
    sstr2
    3ad2ant2
    adantr
    ss2rabdv
    @10
    @7
    intss
    syl
    @3
    @0
    cX
    cA
    wss
    #
    @12
    @8
    wceq
    @0
    @1
    @2
    simp1
    @1
    @2
    @15
    @0
    cX
    cY
    cA
    sstr
    3adant1
    vy
    cA
    @6
    cU
    cK
    cV
    cX
    pclss.a
    @6
    eqid
    #
    pclss.c
    pclvalN
    syl2anc
    @0
    @2
    @13
    @11
    wceq
    @1
    vy
    cA
    @6
    cU
    cK
    cV
    cY
    pclss.a
    @16
    pclss.c
    pclvalN
    3adant2
    3sstr4d
end
