include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "cpr.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "snssd.mm"
include "lspun.mm"
include "syl3anc.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "a1i.mm"
include "clss.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmsp.mm"
include "3eqtr4d.mm"

theorem lsmpr
  let wph: wff ph
  let c.po: class .(+)
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lsmpr.v: |- V = ( Base ` W )
  assume lsmpr.n: |- N = ( LSpan ` W )
  assume lsmpr.p: |- .(+) = ( LSSum ` W )
  assume lsmpr.w: |- ( ph -> W e. LMod )
  assume lsmpr.x: |- ( ph -> X e. V )
  assume lsmpr.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( N ` { X , Y } ) = ( ( N ` { X } ) .(+) ( N ` { Y } ) ) )

  proof
    wph
    cX
    csn
    #
    cY
    csn
    #
    cun
    #
    cN
    cfv
    #
    @0
    cN
    cfv
    #
    @1
    cN
    cfv
    #
    cun
    cN
    cfv
    #
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @4
    @5
    c.po
    co
    #
    wph
    cW
    clmod
    wcel
    #
    @0
    cV
    wss
    @1
    cV
    wss
    @3
    @6
    wceq
    lsmpr.w
    wph
    cX
    cV
    lsmpr.x
    snssd
    wph
    cY
    cV
    lsmpr.y
    snssd
    @0
    @1
    cN
    cV
    cW
    lsmpr.v
    lsmpr.n
    lspun
    syl3anc
    @8
    @3
    wceq
    wph
    @7
    @2
    cN
    cX
    cY
    df-pr
    fveq2i
    a1i
    wph
    @10
    @4
    cW
    clss
    cfv
    #
    wcel
    #
    @5
    @11
    wcel
    #
    @9
    @6
    wceq
    lsmpr.w
    wph
    @10
    cX
    cV
    wcel
    @12
    lsmpr.w
    lsmpr.x
    @11
    cN
    cV
    cW
    cX
    lsmpr.v
    @11
    eqid
    #
    lsmpr.n
    lspsncl
    syl2anc
    wph
    @10
    cY
    cV
    wcel
    @13
    lsmpr.w
    lsmpr.y
    @11
    cN
    cV
    cW
    cY
    lsmpr.v
    @14
    lsmpr.n
    lspsncl
    syl2anc
    c.po
    @11
    @4
    @5
    cN
    cW
    @14
    lsmpr.n
    lsmpr.p
    lsmsp
    syl3anc
    3eqtr4d
end
