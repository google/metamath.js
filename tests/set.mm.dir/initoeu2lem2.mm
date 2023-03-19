include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cop.mm"
include "cv.mm"
include "weu.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "ovex.mm"
include "eleq1.mm"
include "spcegv.mm"
include "mp1i.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "a1d.mm"
include "3imp.mm"
include "adantr.mm"
include "simpll1.mm"
include "simpll2.mm"
include "3simpb.mm"
include "simplr.mm"
include "simpl32.mm"
include "simpr.mm"
include "initoeu2lem1.mm"
include "imp.mm"
include "syl33anc.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqtr4d.mm"
include "ex.mm"
include "alrimivv.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem initoeu2lem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cX: class X
  let c.op: class .o.
  let cG: class G
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  assume initoeu1.c: |- ( ph -> C e. Cat )
  assume initoeu1.a: |- ( ph -> A e. ( InitO ` C ) )
  assume initoeu2lem.x: |- X = ( Base ` C )
  assume initoeu2lem.h: |- H = ( Hom ` C )
  assume initoeu2lem.i: |- I = ( Iso ` C )
  assume initoeu2lem.o: |- .o. = ( comp ` C )

  disjoint D f
  disjoint F f
  disjoint I f
  disjoint K f
  disjoint H f
  disjoint X f
  disjoint .o. f
  disjoint A f
  disjoint D g
  disjoint F g
  disjoint H g
  disjoint I g
  disjoint K g
  disjoint X g
  disjoint .o. g
  disjoint g ph
  disjoint A g
  disjoint A f
  disjoint B g
  disjoint B f
  disjoint C f
  disjoint C g
  disjoint g ph
  disjoint f ph
  disjoint f g
  disjoint G f
  disjoint A h
  disjoint f h
  disjoint B h
  disjoint D h
  disjoint g h
  disjoint F h
  disjoint H h
  disjoint I h
  disjoint K h
  disjoint X h
  disjoint .o. h
  disjoint h ph
  disjoint A a
  disjoint a g
  disjoint A b
  disjoint b f
  disjoint B a
  disjoint B b
  disjoint C b
  disjoint C a
  disjoint a f
  assert |- ( ( ph /\ ( A e. X /\ B e. X /\ D e. X ) /\ ( K e. ( B I A ) /\ F e. ( A H D ) /\ ( F ( <. B , A >. .o. D ) K ) e. ( B H D ) ) ) -> ( E! f f e. ( A H D ) -> E! g g e. ( B H D ) ) )

  proof
    wph
    cA
    cX
    wcel
    cB
    cX
    wcel
    cD
    cX
    wcel
    w3a
    #
    cK
    cB
    cA
    cI
    co
    wcel
    #
    cF
    cA
    cD
    cH
    co
    #
    wcel
    #
    cF
    cK
    cB
    cA
    cop
    cD
    c.op
    co
    #
    co
    #
    cB
    cD
    cH
    co
    #
    wcel
    #
    w3a
    #
    w3a
    #
    vf
    cv
    @2
    wcel
    vf
    weu
    #
    vg
    cv
    #
    @6
    wcel
    #
    vg
    weu
    #
    @9
    @10
    wa
    #
    @12
    vg
    wex
    #
    @12
    vh
    cv
    #
    @6
    wcel
    #
    wa
    #
    @11
    @16
    wceq
    #
    wi
    #
    vh
    wal
    vg
    wal
    @13
    @9
    @15
    @10
    wph
    @0
    @8
    @15
    wph
    @8
    @15
    wi
    @0
    @8
    wph
    @15
    @7
    @1
    wph
    @15
    wi
    @3
    wph
    @7
    @15
    @5
    cvv
    wcel
    @7
    @15
    wi
    wph
    cF
    cK
    @4
    ovex
    @12
    @7
    vg
    @5
    cvv
    @11
    @5
    @6
    eleq1
    spcegv
    mp1i
    com12
    3ad2ant3
    com12
    a1d
    3imp
    adantr
    @14
    @20
    vg
    vh
    @14
    @18
    @19
    @14
    @18
    wa
    @11
    @5
    @16
    @14
    @12
    @11
    @5
    wceq
    #
    @17
    @14
    @12
    wa
    wph
    @0
    @1
    @7
    wa
    #
    @10
    @3
    @12
    @21
    wph
    @0
    @8
    @10
    @12
    simpll1
    wph
    @0
    @8
    @10
    @12
    simpll2
    @14
    @22
    @12
    @9
    @22
    @10
    @8
    wph
    @22
    @0
    @1
    @3
    @7
    3simpb
    3ad2ant3
    adantr
    #
    adantr
    @9
    @10
    @12
    simplr
    @14
    @3
    @12
    @1
    @3
    @7
    wph
    @0
    @10
    simpl32
    #
    adantr
    @14
    @12
    simpr
    wph
    @0
    @22
    w3a
    #
    @10
    @3
    @12
    w3a
    @21
    wph
    cA
    cB
    cC
    cD
    vf
    cF
    @11
    cH
    cI
    cK
    cX
    c.op
    initoeu1.c
    initoeu1.a
    initoeu2lem.x
    initoeu2lem.h
    initoeu2lem.i
    initoeu2lem.o
    initoeu2lem1
    imp
    syl33anc
    adantrr
    @14
    @17
    @16
    @5
    wceq
    #
    @12
    @14
    @17
    wa
    wph
    @0
    @22
    @10
    @3
    @17
    @26
    wph
    @0
    @8
    @10
    @17
    simpll1
    wph
    @0
    @8
    @10
    @17
    simpll2
    @14
    @22
    @17
    @23
    adantr
    @9
    @10
    @17
    simplr
    @14
    @3
    @17
    @24
    adantr
    @14
    @17
    simpr
    @25
    @10
    @3
    @17
    w3a
    @26
    wph
    cA
    cB
    cC
    cD
    vf
    cF
    @16
    cH
    cI
    cK
    cX
    c.op
    initoeu1.c
    initoeu1.a
    initoeu2lem.x
    initoeu2lem.h
    initoeu2lem.i
    initoeu2lem.o
    initoeu2lem1
    imp
    syl33anc
    adantrl
    eqtr4d
    ex
    alrimivv
    @12
    @17
    vg
    vh
    @11
    @16
    @6
    eleq1
    eu4
    sylanbrc
    ex
end
