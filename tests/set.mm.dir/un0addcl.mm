include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "wo.mm"
include "wa.mm"
include "cun.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "wi.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sseldi.mm"
include "expr.mm"
include "cc.mm"
include "sselda.mm"
include "addid2d.mm"
include "wss.mm"
include "a1i.mm"
include "eqeltrd.mm"
include "elsni.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "impancom.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "addid1d.mm"
include "simpr.mm"
include "oveq2d.mm"
include "jaod.mm"
include "syl5bi.mm"
include "impr.mm"

theorem un0addcl
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  assume un0addcl.1: |- ( ph -> S C_ CC )
  assume un0addcl.2: |- T = ( S u. { 0 } )
  assume un0addcl.3: |- ( ( ph /\ ( M e. S /\ N e. S ) ) -> ( M + N ) e. S )


  assert |- ( ( ph /\ ( M e. T /\ N e. T ) ) -> ( M + N ) e. T )

  proof
    wph
    cM
    cT
    wcel
    #
    cN
    cT
    wcel
    #
    cM
    cN
    caddc
    co
    #
    cT
    wcel
    #
    @1
    cN
    cS
    wcel
    #
    cN
    cc0
    csn
    #
    wcel
    #
    wo
    #
    wph
    @0
    wa
    #
    @3
    @1
    cN
    cS
    @5
    cun
    #
    wcel
    @7
    cT
    @9
    cN
    un0addcl.2
    eleq2i
    cN
    cS
    @5
    elun
    bitri
    @8
    @4
    @3
    @6
    @0
    wph
    cM
    cS
    wcel
    #
    cM
    @5
    wcel
    #
    wo
    #
    @4
    @3
    wi
    #
    @0
    cM
    @9
    wcel
    @12
    cT
    @9
    cM
    un0addcl.2
    eleq2i
    cM
    cS
    @5
    elun
    bitri
    wph
    @10
    @13
    @11
    wph
    @10
    @4
    @3
    wph
    @10
    @4
    wa
    wa
    cS
    cT
    @2
    cS
    @9
    cT
    cS
    @5
    ssun1
    un0addcl.2
    sseqtr4i
    #
    un0addcl.3
    sseldi
    expr
    wph
    @4
    @11
    @3
    wph
    @4
    wa
    #
    @3
    @11
    cc0
    cN
    caddc
    co
    #
    cT
    wcel
    @15
    @16
    cN
    cT
    @15
    cN
    wph
    cS
    cc
    cN
    un0addcl.1
    sselda
    addid2d
    wph
    cS
    cT
    cN
    cS
    cT
    wss
    wph
    @14
    a1i
    sselda
    eqeltrd
    @11
    @2
    @16
    cT
    @11
    cM
    cc0
    cN
    caddc
    cM
    cc0
    elsni
    oveq1d
    eleq1d
    syl5ibrcom
    impancom
    jaodan
    sylan2b
    @8
    @3
    @6
    cM
    cc0
    caddc
    co
    #
    cT
    wcel
    @8
    @17
    cM
    cT
    @8
    cM
    wph
    cT
    cc
    cM
    wph
    cT
    @9
    cc
    un0addcl.2
    wph
    cS
    @5
    cc
    un0addcl.1
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    syl5eqss
    sselda
    addid1d
    wph
    @0
    simpr
    eqeltrd
    @6
    @2
    @17
    cT
    @6
    cN
    cc0
    cM
    caddc
    cN
    cc0
    elsni
    oveq2d
    eleq1d
    syl5ibrcom
    jaod
    syl5bi
    impr
end
