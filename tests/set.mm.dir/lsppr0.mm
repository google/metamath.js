include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "clsm.mm"
include "co.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "lsmpr.mm"
include "wceq.mm"
include "lspsn0.mm"
include "oveq2d.mm"
include "csubg.mm"
include "lspsnsubg.mm"
include "syl2anc.mm"
include "lsm01.mm"
include "3eqtrd.mm"

theorem lsppr0
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lsppr0.v: |- V = ( Base ` W )
  assume lsppr0.z: |- .0. = ( 0g ` W )
  assume lsppr0.n: |- N = ( LSpan ` W )
  assume lsppr0.w: |- ( ph -> W e. LMod )
  assume lsppr0.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( N ` { X , .0. } ) = ( N ` { X } ) )

  proof
    wph
    cX
    c.0
    cpr
    cN
    cfv
    cX
    csn
    cN
    cfv
    #
    c.0
    csn
    #
    cN
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    @0
    @1
    @3
    co
    #
    @0
    wph
    @3
    cN
    cV
    cW
    cX
    c.0
    lsppr0.v
    lsppr0.n
    @3
    eqid
    #
    lsppr0.w
    lsppr0.x
    wph
    cW
    clmod
    wcel
    #
    c.0
    cV
    wcel
    lsppr0.w
    cV
    cW
    c.0
    lsppr0.v
    lsppr0.z
    lmod0vcl
    syl
    lsmpr
    wph
    @2
    @1
    @0
    @3
    wph
    @6
    @2
    @1
    wceq
    lsppr0.w
    cN
    cW
    c.0
    lsppr0.z
    lsppr0.n
    lspsn0
    syl
    oveq2d
    wph
    @0
    cW
    csubg
    cfv
    wcel
    #
    @4
    @0
    wceq
    wph
    @6
    cX
    cV
    wcel
    @7
    lsppr0.w
    lsppr0.x
    cN
    cV
    cW
    cX
    lsppr0.v
    lsppr0.n
    lspsnsubg
    syl2anc
    @3
    cW
    @0
    c.0
    lsppr0.z
    @5
    lsm01
    syl
    3eqtrd
end
