include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "gneispacess.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "rspccv.mm"
include "syl.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "sseq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl6.mm"
include "3impd.mm"
include "imp31.mm"

theorem gneispacess2
  let cA: class A
  let cP: class P
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vp: setvar p
  assume gneispace.a: |- A = { f | ( f : dom f --> ( ~P ( ~P dom f \ { (/) } ) \ { (/) } ) /\ A. p e. dom f A. n e. ( f ` p ) ( p e. n /\ A. s e. ~P dom f ( n C_ s -> s e. ( f ` p ) ) ) ) }

  disjoint F n
  disjoint F p
  disjoint n p
  disjoint F f
  disjoint F s
  disjoint f s
  disjoint f n
  disjoint f p
  disjoint P p
  disjoint P n
  disjoint N n
  disjoint S s
  disjoint n s
  disjoint N s
  disjoint p s
  disjoint P s
  assert |- ( ( ( F e. A /\ P e. dom F ) /\ ( N e. ( F ` P ) /\ S e. ~P dom F /\ N C_ S ) ) -> S e. ( F ` P ) )

  proof
    cF
    cA
    wcel
    #
    cP
    cF
    cdm
    #
    wcel
    #
    cN
    cP
    cF
    cfv
    #
    wcel
    #
    cS
    @1
    cpw
    #
    wcel
    #
    cN
    cS
    wss
    #
    w3a
    #
    cS
    @3
    wcel
    #
    @0
    @2
    vn
    cv
    #
    vs
    cv
    #
    wss
    #
    @11
    @3
    wcel
    #
    wi
    #
    vs
    @5
    wral
    #
    vn
    @3
    wral
    #
    @8
    @9
    wi
    @0
    @12
    @11
    vp
    cv
    #
    cF
    cfv
    #
    wcel
    #
    wi
    #
    vs
    @5
    wral
    #
    vn
    @18
    wral
    #
    vp
    @1
    wral
    @2
    @16
    wi
    cA
    vf
    vn
    cF
    vs
    vp
    gneispace.a
    gneispacess
    @22
    @16
    vp
    cP
    @1
    @17
    cP
    wceq
    #
    @21
    @15
    vn
    @18
    @3
    @17
    cP
    cF
    fveq2
    #
    @23
    @20
    @14
    vs
    @5
    @23
    @19
    @13
    @12
    @23
    @18
    @3
    @11
    @24
    eleq2d
    imbi2d
    ralbidv
    raleqbidv
    rspccv
    syl
    @16
    @4
    @6
    @7
    @9
    @16
    @4
    cN
    @11
    wss
    #
    @13
    wi
    #
    vs
    @5
    wral
    #
    @6
    @7
    @9
    wi
    #
    wi
    @15
    @27
    vn
    cN
    @3
    @10
    cN
    wceq
    #
    @14
    @26
    vs
    @5
    @29
    @12
    @25
    @13
    @10
    cN
    @11
    sseq1
    imbi1d
    ralbidv
    rspccv
    @26
    @28
    vs
    cS
    @5
    @11
    cS
    wceq
    @25
    @7
    @13
    @9
    @11
    cS
    cN
    sseq2
    @11
    cS
    @3
    eleq1
    imbi12d
    rspccv
    syl6
    3impd
    syl6
    imp31
end
