include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lssel.mm"
include "syl2anc.mm"
include "lmodcom.mm"
include "syl3anc.mm"
include "lssvancl1.mm"
include "eqneltrrd.mm"

theorem lssvancl2
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


  assert |- ( ph -> -. ( Y .+ X ) e. U )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cY
    cX
    c.pl
    co
    #
    cU
    wph
    cW
    clmod
    wcel
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    @0
    @1
    wceq
    lssvancl.w
    wph
    cU
    cS
    wcel
    cX
    cU
    wcel
    @2
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
    c.pl
    cV
    cW
    cX
    cY
    lssvancl.v
    lssvancl.p
    lmodcom
    syl3anc
    wph
    c.pl
    cS
    cU
    cV
    cW
    cX
    cY
    lssvancl.v
    lssvancl.p
    lssvancl.s
    lssvancl.w
    lssvancl.u
    lssvancl.x
    lssvancl.y
    lssvancl.n
    lssvancl1
    eqneltrrd
end
