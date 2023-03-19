include "cascl.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "evl1scad.mm"
include "evl1muld.mm"
include "casa.mm"
include "csca.mm"
include "cbs.mm"
include "ccrg.mm"
include "ply1assa.mm"
include "syl.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "simpld.mm"
include "asclmul1.mm"
include "syl3anc.mm"
include "eleq1d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "mpbid.mm"

theorem evl1vsd
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume evl1addd.q: |- O = ( eval1 ` R )
  assume evl1addd.p: |- P = ( Poly1 ` R )
  assume evl1addd.b: |- B = ( Base ` R )
  assume evl1addd.u: |- U = ( Base ` P )
  assume evl1addd.1: |- ( ph -> R e. CRing )
  assume evl1addd.2: |- ( ph -> Y e. B )
  assume evl1addd.3: |- ( ph -> ( M e. U /\ ( ( O ` M ) ` Y ) = V ) )
  assume evl1vsd.4: |- ( ph -> N e. B )
  assume evl1vsd.s: |- .xb = ( .s ` P )
  assume evl1vsd.t: |- .x. = ( .r ` R )


  assert |- ( ph -> ( ( N .xb M ) e. U /\ ( ( O ` ( N .xb M ) ) ` Y ) = ( N .x. V ) ) )

  proof
    wph
    cN
    cP
    cascl
    cfv
    #
    cfv
    #
    cM
    cP
    cmulr
    cfv
    #
    co
    #
    cU
    wcel
    #
    cY
    @3
    cO
    cfv
    #
    cfv
    #
    cN
    cV
    c.x
    co
    #
    wceq
    #
    wa
    cN
    cM
    c.xb
    co
    #
    cU
    wcel
    #
    cY
    @9
    cO
    cfv
    #
    cfv
    #
    @7
    wceq
    #
    wa
    wph
    cB
    cP
    cR
    @2
    c.x
    cU
    @1
    cM
    cO
    cN
    cV
    cY
    evl1addd.q
    evl1addd.p
    evl1addd.b
    evl1addd.u
    evl1addd.1
    evl1addd.2
    wph
    @0
    cB
    cP
    cR
    cU
    cO
    cN
    cY
    evl1addd.q
    evl1addd.p
    evl1addd.b
    @0
    eqid
    #
    evl1addd.u
    evl1addd.1
    evl1vsd.4
    evl1addd.2
    evl1scad
    evl1addd.3
    @2
    eqid
    #
    evl1vsd.t
    evl1muld
    wph
    @4
    @10
    @8
    @13
    wph
    @3
    @9
    cU
    wph
    cP
    casa
    wcel
    #
    cN
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    cM
    cU
    wcel
    #
    @3
    @9
    wceq
    wph
    cR
    ccrg
    wcel
    #
    @16
    evl1addd.1
    cP
    cR
    evl1addd.p
    ply1assa
    syl
    wph
    cN
    cB
    @18
    evl1vsd.4
    wph
    cB
    cR
    cbs
    cfv
    @18
    evl1addd.b
    wph
    cR
    @17
    cbs
    wph
    @20
    cR
    @17
    wceq
    evl1addd.1
    cP
    cR
    ccrg
    evl1addd.p
    ply1sca
    syl
    fveq2d
    syl5eq
    eleqtrd
    wph
    @19
    cY
    cM
    cO
    cfv
    cfv
    cV
    wceq
    evl1addd.3
    simpld
    @0
    cN
    c.xb
    @2
    @17
    @18
    cU
    cP
    cM
    @14
    @17
    eqid
    @18
    eqid
    evl1addd.u
    @15
    evl1vsd.s
    asclmul1
    syl3anc
    #
    eleq1d
    wph
    @6
    @12
    @7
    wph
    cY
    @5
    @11
    wph
    @3
    @9
    cO
    @21
    fveq2d
    fveq1d
    eqeq1d
    anbi12d
    mpbid
end
