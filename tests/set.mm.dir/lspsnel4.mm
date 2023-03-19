include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "csn.mm"
include "cfv.mm"
include "lspsnel3.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "lspsneleq.mm"
include "eleqtrrd.mm"
include "impbida.mm"

theorem lspsnel4
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspsnel4.v: |- V = ( Base ` W )
  assume lspsnel4.o: |- .0. = ( 0g ` W )
  assume lspsnel4.s: |- S = ( LSubSp ` W )
  assume lspsnel4.n: |- N = ( LSpan ` W )
  assume lspsnel4.w: |- ( ph -> W e. LVec )
  assume lspsnel4.u: |- ( ph -> U e. S )
  assume lspsnel4.x: |- ( ph -> X e. V )
  assume lspsnel4.y: |- ( ph -> Y e. ( N ` { X } ) )
  assume lspsnel4.z: |- ( ph -> Y =/= .0. )


  assert |- ( ph -> ( X e. U <-> Y e. U ) )

  proof
    wph
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    wph
    @0
    wa
    cS
    cU
    cN
    cW
    cX
    cY
    lspsnel4.s
    lspsnel4.n
    wph
    cW
    clmod
    wcel
    #
    @0
    wph
    cW
    clvec
    wcel
    @2
    lspsnel4.w
    cW
    lveclmod
    syl
    #
    adantr
    wph
    cU
    cS
    wcel
    #
    @0
    lspsnel4.u
    adantr
    wph
    @0
    simpr
    wph
    cY
    cX
    csn
    cN
    cfv
    #
    wcel
    @0
    lspsnel4.y
    adantr
    lspsnel3
    wph
    @1
    wa
    cS
    cU
    cN
    cW
    cY
    cX
    lspsnel4.s
    lspsnel4.n
    wph
    @2
    @1
    @3
    adantr
    wph
    @4
    @1
    lspsnel4.u
    adantr
    wph
    @1
    simpr
    wph
    cX
    cY
    csn
    cN
    cfv
    #
    wcel
    @1
    wph
    cX
    @5
    @6
    wph
    @2
    cX
    cV
    wcel
    cX
    @5
    wcel
    @3
    lspsnel4.x
    cN
    cV
    cW
    cX
    lspsnel4.v
    lspsnel4.n
    lspsnid
    syl2anc
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    lspsnel4.v
    lspsnel4.o
    lspsnel4.n
    lspsnel4.w
    lspsnel4.x
    lspsnel4.y
    lspsnel4.z
    lspsneleq
    eleqtrrd
    adantr
    lspsnel3
    impbida
end
