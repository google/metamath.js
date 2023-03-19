include "co.mm"
include "wcel.mm"
include "wa.mm"
include "csg.mm"
include "cfv.mm"
include "wceq.mm"
include "cabl.mm"
include "clmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "lssel.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ablpncan2.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "mtand.mm"

theorem lssvancl1
  let wph: wff ph
  let c.pl: class .+
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lssvancl.v: |- V = ( Base ` W )
  assume lssvancl.p: |- .+ = ( +g ` W )
  assume lssvancl.s: |- S = ( LSubSp ` W )
  assume lssvancl.w: |- ( ph -> W e. LMod )
  assume lssvancl.u: |- ( ph -> U e. S )
  assume lssvancl.x: |- ( ph -> X e. U )
  assume lssvancl.y: |- ( ph -> Y e. V )
  assume lssvancl.n: |- ( ph -> -. Y e. U )


  assert |- ( ph -> -. ( X .+ Y ) e. U )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cU
    wcel
    #
    cY
    cU
    wcel
    lssvancl.n
    wph
    @1
    wa
    #
    @0
    cX
    cW
    csg
    cfv
    #
    co
    #
    cY
    cU
    wph
    @4
    cY
    wceq
    #
    @1
    wph
    cW
    cabl
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    @5
    wph
    cW
    clmod
    wcel
    #
    @6
    lssvancl.w
    cW
    lmodabl
    syl
    wph
    cU
    cS
    wcel
    #
    cX
    cU
    wcel
    #
    @7
    lssvancl.u
    lssvancl.x
    cS
    cU
    cV
    cW
    cX
    lssvancl.v
    lssvancl.s
    lssel
    syl2anc
    lssvancl.y
    cV
    c.pl
    cW
    @3
    cX
    cY
    lssvancl.v
    lssvancl.p
    @3
    eqid
    #
    ablpncan2
    syl3anc
    adantr
    @2
    @8
    @9
    @1
    @10
    @4
    cU
    wcel
    wph
    @8
    @1
    lssvancl.w
    adantr
    wph
    @9
    @1
    lssvancl.u
    adantr
    wph
    @1
    simpr
    wph
    @10
    @1
    lssvancl.x
    adantr
    cS
    cU
    @3
    cW
    @0
    cX
    @11
    lssvancl.s
    lssvsubcl
    syl22anc
    eqeltrrd
    mtand
end
