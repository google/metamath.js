include "cwdom.mm"
include "wbr.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cdm.mm"
include "wral.mm"
include "cxp.mm"
include "char.mm"
include "cfv.mm"
include "wss.mm"
include "cdom.mm"
include "wdomref.mm"
include "xpwdomg.mm"
include "sylan2.mm"
include "wdompwdom.mm"
include "harword.mm"
include "3syl.mm"
include "adantr.mm"
include "cvv.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "simplr.mm"
include "simpr.mm"
include "hsmexlem2.mm"
include "syl3anc.mm"
include "sseldd.mm"

theorem hsmexlem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let cV: class V
  assume hsmexlem.f: |- F = OrdIso ( _E , B )
  assume hsmexlem.g: |- G = OrdIso ( _E , U_ a e. A B )

  disjoint A a
  disjoint C a
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint A c
  disjoint d e
  disjoint A d
  disjoint A e
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint V b
  disjoint V c
  assert |- ( ( ( A ~<_* D /\ C e. On ) /\ A. a e. A ( B e. ~P On /\ dom F e. C ) ) -> dom G e. ( har ` ~P ( D X. C ) ) )

  proof
    cA
    cD
    cwdom
    wbr
    #
    cC
    con0
    wcel
    #
    wa
    #
    cB
    con0
    cpw
    wcel
    cF
    cdm
    cC
    wcel
    wa
    va
    cA
    wral
    #
    wa
    #
    cA
    cC
    cxp
    #
    cpw
    #
    char
    cfv
    #
    cD
    cC
    cxp
    #
    cpw
    #
    char
    cfv
    #
    cG
    cdm
    #
    @2
    @7
    @10
    wss
    #
    @3
    @2
    @5
    @8
    cwdom
    wbr
    #
    @6
    @9
    cdom
    wbr
    @12
    @1
    @0
    cC
    cC
    cwdom
    wbr
    @13
    con0
    cC
    wdomref
    cA
    cD
    cC
    cC
    xpwdomg
    sylan2
    @5
    @8
    wdompwdom
    @6
    @9
    harword
    3syl
    adantr
    @4
    cA
    cvv
    wcel
    #
    @1
    @3
    @11
    @7
    wcel
    @2
    @14
    @3
    @0
    @14
    @1
    cA
    cD
    cwdom
    relwdom
    brrelexi
    adantr
    adantr
    @0
    @1
    @3
    simplr
    @2
    @3
    simpr
    cA
    cB
    cC
    cF
    cG
    cvv
    va
    hsmexlem.f
    hsmexlem.g
    hsmexlem2
    syl3anc
    sseldd
end
