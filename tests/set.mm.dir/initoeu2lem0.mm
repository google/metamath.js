include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cop.mm"
include "cinv.mm"
include "cfv.mm"
include "wceq.mm"
include "3simpa.mm"
include "simp3.mm"
include "eqcomd.mm"
include "eqid.mm"
include "ccat.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simplr3.mm"
include "ciso.mm"
include "oveqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "chom.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "isohom.mm"
include "sseld.mm"
include "com12.mm"
include "impcom.mm"
include "3ad2ant2.mm"
include "catcocl.mm"
include "cco.mm"
include "rcaninv.mm"
include "sylc.mm"

theorem initoeu2lem0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cX: class X
  let c.op: class .o.
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  assume initoeu1.c: |- ( ph -> C e. Cat )
  assume initoeu1.a: |- ( ph -> A e. ( InitO ` C ) )
  assume initoeu2lem.x: |- X = ( Base ` C )
  assume initoeu2lem.h: |- H = ( Hom ` C )
  assume initoeu2lem.i: |- I = ( Iso ` C )
  assume initoeu2lem.o: |- .o. = ( comp ` C )


  assert |- ( ( ( ph /\ ( A e. X /\ B e. X /\ D e. X ) ) /\ ( K e. ( B I A ) /\ F e. ( A H D ) /\ G e. ( B H D ) ) /\ ( ( F ( <. B , A >. .o. D ) K ) ( <. A , B >. .o. D ) ( ( B ( Inv ` C ) A ) ` K ) ) = ( G ( <. A , B >. .o. D ) ( ( B ( Inv ` C ) A ) ` K ) ) ) -> G = ( F ( <. B , A >. .o. D ) K ) )

  proof
    wph
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cD
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cK
    cB
    cA
    cI
    co
    #
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
    cG
    cB
    cD
    cH
    co
    #
    wcel
    #
    w3a
    #
    cF
    cK
    cB
    cA
    cop
    cD
    c.op
    co
    co
    #
    cK
    cB
    cA
    cC
    cinv
    cfv
    #
    co
    cfv
    #
    cA
    cB
    cop
    #
    cD
    c.op
    co
    #
    co
    #
    cG
    @14
    @16
    co
    #
    wceq
    #
    w3a
    #
    @4
    @11
    wa
    #
    @18
    @17
    wceq
    cG
    @12
    wceq
    @4
    @11
    @19
    3simpa
    @20
    @17
    @18
    @4
    @11
    @19
    simp3
    eqcomd
    @21
    cX
    cC
    @14
    cK
    cG
    @12
    @13
    cA
    cB
    @16
    cD
    initoeu2lem.x
    @13
    eqid
    @4
    cC
    ccat
    wcel
    #
    @11
    wph
    @22
    @3
    initoeu1.c
    adantr
    #
    adantr
    #
    @4
    @0
    @11
    wph
    @0
    @1
    @2
    simpr1
    #
    adantr
    #
    @4
    @1
    @11
    wph
    @0
    @1
    @2
    simpr2
    #
    adantr
    #
    @0
    @1
    @2
    wph
    @11
    simplr3
    #
    @11
    cK
    cB
    cA
    cC
    ciso
    cfv
    #
    co
    #
    wcel
    #
    @4
    @6
    @8
    @32
    @10
    @6
    @32
    @5
    @31
    cK
    cI
    @30
    cB
    cA
    initoeu2lem.i
    oveqi
    eleq2i
    biimpi
    3ad2ant1
    adantl
    @11
    cG
    cB
    cD
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    @4
    @10
    @6
    @35
    @8
    @10
    @35
    @9
    @34
    cG
    cH
    @33
    cB
    cD
    initoeu2lem.h
    oveqi
    eleq2i
    biimpi
    3ad2ant3
    adantl
    @21
    cX
    cC
    c.op
    cK
    cF
    @33
    cB
    cA
    cD
    initoeu2lem.x
    @33
    eqid
    #
    initoeu2lem.o
    @24
    @28
    @26
    @29
    @11
    @4
    cK
    cB
    cA
    @33
    co
    #
    wcel
    #
    @6
    @8
    @4
    @38
    wi
    @10
    @4
    @6
    @38
    @4
    @5
    @37
    cK
    @4
    cX
    cC
    @33
    cI
    cB
    cA
    initoeu2lem.x
    @36
    initoeu2lem.i
    @23
    @27
    @25
    isohom
    sseld
    com12
    3ad2ant1
    impcom
    @11
    cF
    cA
    cD
    @33
    co
    #
    wcel
    #
    @4
    @8
    @6
    @40
    @10
    @8
    @40
    @7
    @39
    cF
    cH
    @33
    cA
    cD
    initoeu2lem.h
    oveqi
    eleq2i
    biimpi
    3ad2ant2
    adantl
    catcocl
    @14
    eqid
    c.op
    cC
    cco
    cfv
    @15
    cD
    initoeu2lem.o
    oveqi
    rcaninv
    sylc
end
