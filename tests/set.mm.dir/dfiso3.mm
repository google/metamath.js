include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "ccid.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wbr.mm"
include "eqid.mm"
include "dfiso2.mm"
include "ccat.mm"
include "adantr.mm"
include "simpr.mm"
include "issect2.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6rbb.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem dfiso3
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  assume dfiso3.b: |- B = ( Base ` C )
  assume dfiso3.h: |- H = ( Hom ` C )
  assume dfiso3.i: |- I = ( Iso ` C )
  assume dfiso3.s: |- S = ( Sect ` C )
  assume dfiso3.c: |- ( ph -> C e. Cat )
  assume dfiso3.x: |- ( ph -> X e. B )
  assume dfiso3.y: |- ( ph -> Y e. B )
  assume dfiso3.f: |- ( ph -> F e. ( X H Y ) )

  disjoint C g
  disjoint F g
  disjoint H g
  disjoint I g
  disjoint X g
  disjoint Y g
  disjoint g ph
  assert |- ( ph -> ( F e. ( X I Y ) <-> E. g e. ( Y H X ) ( g ( Y S X ) F /\ F ( X S Y ) g ) ) )

  proof
    wph
    cF
    cX
    cY
    cI
    co
    wcel
    vg
    cv
    #
    cF
    cX
    cY
    cop
    cX
    cC
    cco
    cfv
    #
    co
    #
    co
    cX
    cC
    ccid
    cfv
    #
    cfv
    wceq
    #
    cF
    @0
    cY
    cX
    cop
    cY
    @1
    co
    #
    co
    cY
    @3
    cfv
    wceq
    #
    wa
    #
    vg
    cY
    cX
    cH
    co
    #
    wrex
    @0
    cF
    cY
    cX
    cS
    co
    wbr
    #
    cF
    @0
    cX
    cY
    cS
    co
    wbr
    #
    wa
    #
    vg
    @8
    wrex
    wph
    cB
    cC
    @3
    vg
    cF
    cH
    cI
    @5
    cX
    cY
    @2
    dfiso3.b
    dfiso3.h
    dfiso3.c
    dfiso3.i
    dfiso3.x
    dfiso3.y
    dfiso3.f
    @3
    eqid
    #
    @2
    eqid
    @5
    eqid
    dfiso2
    wph
    @7
    @11
    vg
    @8
    wph
    @0
    @8
    wcel
    #
    wa
    #
    @11
    @6
    @4
    wa
    @7
    @14
    @9
    @6
    @10
    @4
    @14
    cB
    cC
    cS
    @1
    @3
    @0
    cF
    cH
    cY
    cX
    dfiso3.b
    dfiso3.h
    @1
    eqid
    #
    @12
    dfiso3.s
    wph
    cC
    ccat
    wcel
    @13
    dfiso3.c
    adantr
    #
    wph
    cY
    cB
    wcel
    @13
    dfiso3.y
    adantr
    #
    wph
    cX
    cB
    wcel
    @13
    dfiso3.x
    adantr
    #
    wph
    @13
    simpr
    #
    wph
    cF
    cX
    cY
    cH
    co
    wcel
    @13
    dfiso3.f
    adantr
    #
    issect2
    @14
    cB
    cC
    cS
    @1
    @3
    cF
    @0
    cH
    cX
    cY
    dfiso3.b
    dfiso3.h
    @15
    @12
    dfiso3.s
    @16
    @18
    @17
    @20
    @19
    issect2
    anbi12d
    @6
    @4
    ancom
    syl6rbb
    rexbidva
    bitrd
end
