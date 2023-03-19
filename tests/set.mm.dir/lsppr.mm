include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "clsm.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "snssd.mm"
include "lspun.mm"
include "syl3anc.mm"
include "clss.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmsp.mm"
include "lsmspsn.mm"
include "abbi2dv.mm"
include "3eqtr2d.mm"
include "syl5eq.mm"

theorem lsppr
  let wph: wff ph
  let vv: setvar v
  let c.pl: class .+
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vl: setvar l
  assume lsppr.v: |- V = ( Base ` W )
  assume lsppr.a: |- .+ = ( +g ` W )
  assume lsppr.f: |- F = ( Scalar ` W )
  assume lsppr.k: |- K = ( Base ` F )
  assume lsppr.t: |- .x. = ( .s ` W )
  assume lsppr.n: |- N = ( LSpan ` W )
  assume lsppr.w: |- ( ph -> W e. LMod )
  assume lsppr.x: |- ( ph -> X e. V )
  assume lsppr.y: |- ( ph -> Y e. V )

  disjoint k l
  disjoint .+ k
  disjoint .+ l
  disjoint F k
  disjoint F l
  disjoint K k
  disjoint K l
  disjoint k v
  disjoint N k
  disjoint l v
  disjoint N l
  disjoint N v
  disjoint .x. k
  disjoint .x. l
  disjoint V k
  disjoint V l
  disjoint W k
  disjoint W l
  disjoint W v
  disjoint X k
  disjoint X l
  disjoint X v
  disjoint Y k
  disjoint Y l
  disjoint Y v
  disjoint k ph
  disjoint l ph
  disjoint ph v
  assert |- ( ph -> ( N ` { X , Y } ) = { v | E. k e. K E. l e. K v = ( ( k .x. X ) .+ ( l .x. Y ) ) } )

  proof
    wph
    cX
    cY
    cpr
    #
    cN
    cfv
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
    vv
    cv
    #
    vk
    cv
    cX
    c.x
    co
    vl
    cv
    cY
    c.x
    co
    c.pl
    co
    wceq
    vl
    cK
    wrex
    vk
    cK
    wrex
    #
    vv
    cab
    #
    @0
    @3
    cN
    cX
    cY
    df-pr
    fveq2i
    wph
    @4
    @1
    cN
    cfv
    #
    @2
    cN
    cfv
    #
    cun
    cN
    cfv
    #
    @8
    @9
    cW
    clsm
    cfv
    #
    co
    #
    @7
    wph
    cW
    clmod
    wcel
    #
    @1
    cV
    wss
    @2
    cV
    wss
    @4
    @10
    wceq
    lsppr.w
    wph
    cX
    cV
    lsppr.x
    snssd
    wph
    cY
    cV
    lsppr.y
    snssd
    @1
    @2
    cN
    cV
    cW
    lsppr.v
    lsppr.n
    lspun
    syl3anc
    wph
    @13
    @8
    cW
    clss
    cfv
    #
    wcel
    #
    @9
    @14
    wcel
    #
    @12
    @10
    wceq
    lsppr.w
    wph
    @13
    cX
    cV
    wcel
    @15
    lsppr.w
    lsppr.x
    @14
    cN
    cV
    cW
    cX
    lsppr.v
    @14
    eqid
    #
    lsppr.n
    lspsncl
    syl2anc
    wph
    @13
    cY
    cV
    wcel
    @16
    lsppr.w
    lsppr.y
    @14
    cN
    cV
    cW
    cY
    lsppr.v
    @17
    lsppr.n
    lspsncl
    syl2anc
    @11
    @14
    @8
    @9
    cN
    cW
    @17
    lsppr.n
    @11
    eqid
    #
    lsmsp
    syl3anc
    wph
    @6
    vv
    @12
    wph
    c.pl
    @11
    c.x
    @5
    vk
    vl
    cF
    cK
    cN
    cV
    cW
    cX
    cY
    lsppr.v
    lsppr.a
    lsppr.f
    lsppr.k
    lsppr.t
    @18
    lsppr.n
    lsppr.w
    lsppr.x
    lsppr.y
    lsmspsn
    abbi2dv
    3eqtr2d
    syl5eq
end
