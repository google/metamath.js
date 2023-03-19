include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "lssel.mm"
include "sylan.mm"
include "clmod.mm"
include "adantr.mm"
include "simpr.mm"
include "lspsnss.mm"
include "syl3anc.mm"
include "jca.mm"
include "lspsnid.mm"
include "ssel.mm"
include "syl5com.mm"
include "impr.mm"
include "impbida.mm"

theorem lspsnel6
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lspsnel5.v: |- V = ( Base ` W )
  assume lspsnel5.s: |- S = ( LSubSp ` W )
  assume lspsnel5.n: |- N = ( LSpan ` W )
  assume lspsnel5.w: |- ( ph -> W e. LMod )
  assume lspsnel5.a: |- ( ph -> U e. S )


  assert |- ( ph -> ( X e. U <-> ( X e. V /\ ( N ` { X } ) C_ U ) ) )

  proof
    wph
    cX
    cU
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    csn
    cN
    cfv
    #
    cU
    wss
    #
    wa
    wph
    @0
    wa
    #
    @1
    @3
    wph
    cU
    cS
    wcel
    #
    @0
    @1
    lspsnel5.a
    cS
    cU
    cV
    cW
    cX
    lspsnel5.v
    lspsnel5.s
    lssel
    sylan
    @4
    cW
    clmod
    wcel
    #
    @5
    @0
    @3
    wph
    @6
    @0
    lspsnel5.w
    adantr
    wph
    @5
    @0
    lspsnel5.a
    adantr
    wph
    @0
    simpr
    cS
    cU
    cN
    cW
    cX
    lspsnel5.s
    lspsnel5.n
    lspsnss
    syl3anc
    jca
    wph
    @1
    @3
    @0
    wph
    @1
    wa
    cX
    @2
    wcel
    #
    @3
    @0
    wph
    @6
    @1
    @7
    lspsnel5.w
    cN
    cV
    cW
    cX
    lspsnel5.v
    lspsnel5.n
    lspsnid
    sylan
    @2
    cU
    cX
    ssel
    syl5com
    impr
    impbida
end
