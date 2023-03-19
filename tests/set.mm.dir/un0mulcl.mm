include "wcel.mm"
include "cmul.mm"
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
include "mul02d.mm"
include "wss.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "syl6eqel.mm"
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
include "mul01d.mm"
include "oveq2d.mm"
include "jaod.mm"
include "syl5bi.mm"
include "impr.mm"

theorem un0mulcl
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  assume un0addcl.1: |- ( ph -> S C_ CC )
  assume un0addcl.2: |- T = ( S u. { 0 } )
  assume un0mulcl.3: |- ( ( ph /\ ( M e. S /\ N e. S ) ) -> ( M x. N ) e. S )


  assert |- ( ( ph /\ ( M e. T /\ N e. T ) ) -> ( M x. N ) e. T )

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
    cmul
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
    un0mulcl.3
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
    cmul
    co
    #
    cT
    wcel
    @14
    @15
    cc0
    cT
    @14
    cN
    wph
    cS
    cc
    cN
    un0addcl.1
    sselda
    mul02d
    cc0
    cT
    wcel
    @5
    cT
    wss
    @5
    @9
    cT
    @5
    cS
    ssun2
    un0addcl.2
    sseqtr4i
    cc0
    cT
    c0ex
    snss
    mpbir
    #
    syl6eqel
    @11
    @2
    @15
    cT
    @11
    cM
    cc0
    cN
    cmul
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
    cmul
    co
    #
    cT
    wcel
    @8
    @17
    cc0
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
    mul01d
    @16
    syl6eqel
    @6
    @2
    @17
    cT
    @6
    cN
    cc0
    cM
    cmul
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
