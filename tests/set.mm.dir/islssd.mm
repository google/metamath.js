include "clss.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wcel.mm"
include "wral.mm"
include "csca.mm"
include "sseqtrd.mm"
include "wa.mm"
include "3exp2.mm"
include "imp43.mm"
include "ralrimivva.mm"
include "ex.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "2ralbidv.mm"
include "3imtr3d.mm"
include "ralrimiv.mm"
include "eqid.mm"
include "islss.mm"
include "syl3anbrc.mm"
include "eleqtrrd.mm"

theorem islssd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume islssd.f: |- ( ph -> F = ( Scalar ` W ) )
  assume islssd.b: |- ( ph -> B = ( Base ` F ) )
  assume islssd.v: |- ( ph -> V = ( Base ` W ) )
  assume islssd.p: |- ( ph -> .+ = ( +g ` W ) )
  assume islssd.t: |- ( ph -> .x. = ( .s ` W ) )
  assume islssd.s: |- ( ph -> S = ( LSubSp ` W ) )
  assume islssd.u: |- ( ph -> U C_ V )
  assume islssd.z: |- ( ph -> U =/= (/) )
  assume islssd.c: |- ( ( ph /\ ( x e. B /\ a e. U /\ b e. U ) ) -> ( ( x .x. a ) .+ b ) e. U )

  disjoint a b
  disjoint a x
  disjoint a ph
  disjoint b x
  disjoint b ph
  disjoint ph x
  disjoint U a
  disjoint U b
  disjoint U x
  disjoint W a
  disjoint W b
  disjoint W x
  disjoint B a
  disjoint B b
  assert |- ( ph -> U e. S )

  proof
    wph
    cU
    cW
    clss
    cfv
    #
    cS
    wph
    cU
    cW
    cbs
    cfv
    #
    wss
    cU
    c0
    wne
    vx
    cv
    #
    va
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    vb
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    cU
    wcel
    #
    vb
    cU
    wral
    va
    cU
    wral
    #
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    cU
    @0
    wcel
    wph
    cU
    cV
    @1
    islssd.u
    islssd.v
    sseqtrd
    islssd.z
    wph
    @10
    vx
    @12
    wph
    @2
    cB
    wcel
    #
    @2
    @3
    c.x
    co
    #
    @6
    c.pl
    co
    #
    cU
    wcel
    #
    vb
    cU
    wral
    va
    cU
    wral
    #
    @2
    @12
    wcel
    @10
    wph
    @13
    @17
    wph
    @13
    wa
    @16
    va
    vb
    cU
    cU
    wph
    @13
    @3
    cU
    wcel
    #
    @6
    cU
    wcel
    #
    @16
    wph
    @13
    @18
    @19
    @16
    islssd.c
    3exp2
    imp43
    ralrimivva
    ex
    wph
    cB
    @12
    @2
    wph
    cB
    cF
    cbs
    cfv
    @12
    islssd.b
    wph
    cF
    @11
    cbs
    islssd.f
    fveq2d
    eqtrd
    eleq2d
    wph
    @16
    @9
    va
    vb
    cU
    cU
    wph
    @15
    @8
    cU
    wph
    @15
    @14
    @6
    @7
    co
    @8
    wph
    c.pl
    @7
    @14
    @6
    islssd.p
    oveqd
    wph
    @14
    @5
    @6
    @7
    wph
    c.x
    @4
    @2
    @3
    islssd.t
    oveqd
    oveq1d
    eqtrd
    eleq1d
    2ralbidv
    3imtr3d
    ralrimiv
    vx
    @12
    @7
    @0
    @4
    cU
    @11
    @1
    cW
    va
    vb
    @11
    eqid
    @12
    eqid
    @1
    eqid
    @7
    eqid
    @4
    eqid
    @0
    eqid
    islss
    syl3anbrc
    islssd.s
    eleqtrrd
end
