include "co.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "csect.mm"
include "cfv.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "adantr.mm"
include "wi.mm"
include "isinv.mm"
include "simpr.mm"
include "syl6bi.mm"
include "com12.mm"
include "impcom.mm"
include "simpl.mm"
include "adantld.mm"
include "imp.mm"
include "sectcan.mm"
include "ex.mm"

theorem inveq
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  assume inveq.b: |- B = ( Base ` C )
  assume inveq.h: |- H = ( Hom ` C )
  assume inveq.n: |- N = ( Inv ` C )
  assume inveq.c: |- ( ph -> C e. Cat )
  assume inveq.x: |- ( ph -> X e. B )
  assume inveq.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( F ( X N Y ) G /\ F ( X N Y ) K ) -> G = K ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cN
    co
    #
    wbr
    #
    cF
    cK
    @0
    wbr
    #
    wa
    #
    cG
    cK
    wceq
    wph
    @3
    wa
    cB
    cC
    cC
    csect
    cfv
    #
    cF
    cG
    cK
    cY
    cX
    inveq.b
    @4
    eqid
    #
    wph
    cC
    ccat
    wcel
    @3
    inveq.c
    adantr
    wph
    cY
    cB
    wcel
    @3
    inveq.y
    adantr
    wph
    cX
    cB
    wcel
    @3
    inveq.x
    adantr
    @3
    wph
    cG
    cF
    cY
    cX
    @4
    co
    #
    wbr
    #
    @1
    wph
    @7
    wi
    @2
    wph
    @1
    @7
    wph
    @1
    cF
    cG
    cX
    cY
    @4
    co
    #
    wbr
    #
    @7
    wa
    @7
    wph
    cB
    cC
    @4
    cF
    cG
    cN
    cX
    cY
    inveq.b
    inveq.n
    inveq.c
    inveq.x
    inveq.y
    @5
    isinv
    @9
    @7
    simpr
    syl6bi
    com12
    adantr
    impcom
    wph
    @3
    cF
    cK
    @8
    wbr
    #
    wph
    @2
    @10
    @1
    wph
    @2
    @10
    cK
    cF
    @6
    wbr
    #
    wa
    @10
    wph
    cB
    cC
    @4
    cF
    cK
    cN
    cX
    cY
    inveq.b
    inveq.n
    inveq.c
    inveq.x
    inveq.y
    @5
    isinv
    @10
    @11
    simpl
    syl6bi
    adantld
    imp
    sectcan
    ex
end
