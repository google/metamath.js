include "clmod.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "lsssubg.mm"
include "lssvscl.mm"
include "ralrimivva.mm"
include "jca.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cplusg.mm"
include "subgss.mm"
include "ad2antrl.mm"
include "c0g.mm"
include "eqid.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "syl.mm"
include "wi.mm"
include "subgcl.mm"
include "3exp.mm"
include "adantl.mm"
include "ralrimdv.mm"
include "ralimdv.mm"
include "impr.mm"
include "islss.mm"
include "syl3anbrc.mm"
include "impbida.mm"

theorem islss4
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume islss4.f: |- F = ( Scalar ` W )
  assume islss4.b: |- B = ( Base ` F )
  assume islss4.v: |- V = ( Base ` W )
  assume islss4.t: |- .x. = ( .s ` W )
  assume islss4.s: |- S = ( LSubSp ` W )

  disjoint F a
  disjoint F b
  disjoint a b
  disjoint W a
  disjoint W b
  disjoint B a
  disjoint B b
  disjoint V a
  disjoint V b
  disjoint .x. a
  disjoint .x. b
  disjoint S a
  disjoint S b
  disjoint U a
  disjoint U b
  disjoint F c
  disjoint a c
  disjoint b c
  disjoint W c
  disjoint B c
  disjoint V c
  disjoint .x. c
  disjoint S c
  disjoint U c
  assert |- ( W e. LMod -> ( U e. S <-> ( U e. ( SubGrp ` W ) /\ A. a e. B A. b e. U ( a .x. b ) e. U ) ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    cU
    cW
    csubg
    cfv
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    c.x
    co
    #
    cU
    wcel
    #
    vb
    cU
    wral
    #
    va
    cB
    wral
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @8
    cS
    cU
    cW
    islss4.s
    lsssubg
    @10
    @6
    va
    vb
    cB
    cU
    cB
    cS
    c.x
    cU
    cF
    cW
    @3
    @4
    islss4.f
    islss4.t
    islss4.b
    islss4.s
    lssvscl
    ralrimivva
    jca
    @0
    @9
    wa
    cU
    cV
    wss
    #
    cU
    c0
    wne
    #
    @5
    vc
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    cU
    wcel
    #
    vc
    cU
    wral
    #
    vb
    cU
    wral
    #
    va
    cB
    wral
    #
    @1
    @2
    @11
    @0
    @8
    cV
    cU
    cW
    islss4.v
    subgss
    ad2antrl
    @2
    @12
    @0
    @8
    @2
    cW
    c0g
    cfv
    #
    cU
    wcel
    @12
    cU
    cW
    @19
    @19
    eqid
    subg0cl
    cU
    @19
    ne0i
    syl
    ad2antrl
    @0
    @2
    @8
    @18
    @0
    @2
    wa
    #
    @7
    @17
    va
    cB
    @20
    @6
    @16
    vb
    cU
    @20
    @6
    @15
    vc
    cU
    @2
    @6
    @13
    cU
    wcel
    #
    @15
    wi
    wi
    @0
    @2
    @6
    @21
    @15
    @14
    cU
    cW
    @5
    @13
    @14
    eqid
    #
    subgcl
    3exp
    adantl
    ralrimdv
    ralimdv
    ralimdv
    impr
    va
    cB
    @14
    cS
    c.x
    cU
    cF
    cV
    cW
    vb
    vc
    islss4.f
    islss4.b
    islss4.v
    @22
    islss4.t
    islss4.s
    islss
    syl3anbrc
    impbida
end
