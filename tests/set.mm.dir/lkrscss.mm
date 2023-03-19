include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "wss.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lkrssv.mm"
include "eqid.mm"
include "lfl0sc.mm"
include "fveq2d.mm"
include "wb.mm"
include "lfl0f.mm"
include "lkr0f.mm"
include "syl2anc.mm"
include "mpbiri.mm"
include "eqtr2d.mm"
include "sseqtrd.mm"
include "adantr.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "oveq2d.mm"
include "adantl.mm"
include "sseqtr4d.mm"
include "wne.mm"
include "simpr.mm"
include "lkrsc.mm"
include "eqimss2.mm"
include "pm2.61dane.mm"

theorem lkrscss
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume lkrsc.v: |- V = ( Base ` W )
  assume lkrsc.d: |- D = ( Scalar ` W )
  assume lkrsc.k: |- K = ( Base ` D )
  assume lkrsc.t: |- .x. = ( .r ` D )
  assume lkrsc.f: |- F = ( LFnl ` W )
  assume lkrsc.l: |- L = ( LKer ` W )
  assume lkrsc.w: |- ( ph -> W e. LVec )
  assume lkrsc.g: |- ( ph -> G e. F )
  assume lkrsc.r: |- ( ph -> R e. K )


  assert |- ( ph -> ( L ` G ) C_ ( L ` ( G oF .x. ( V X. { R } ) ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    cG
    cV
    cR
    csn
    #
    cxp
    #
    c.x
    cof
    #
    co
    #
    cL
    cfv
    #
    wss
    #
    cR
    cD
    c0g
    cfv
    #
    wph
    cR
    @7
    wceq
    #
    wa
    @0
    cG
    cV
    @7
    csn
    #
    cxp
    #
    @3
    co
    #
    cL
    cfv
    #
    @5
    wph
    @0
    @12
    wss
    @8
    wph
    @0
    cV
    @12
    wph
    cF
    cG
    cL
    cV
    cW
    lkrsc.v
    lkrsc.f
    lkrsc.l
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    lkrsc.w
    cW
    lveclmod
    syl
    #
    lkrsc.g
    lkrssv
    wph
    @12
    @10
    cL
    cfv
    #
    cV
    wph
    @11
    @10
    cL
    wph
    cD
    c.x
    cF
    cG
    cK
    cV
    cW
    @7
    lkrsc.v
    lkrsc.d
    lkrsc.f
    lkrsc.k
    lkrsc.t
    @7
    eqid
    #
    @15
    lkrsc.g
    lfl0sc
    fveq2d
    wph
    @16
    cV
    wceq
    #
    @10
    @10
    wceq
    #
    @10
    eqid
    wph
    @14
    @10
    cF
    wcel
    #
    @18
    @19
    wb
    @15
    wph
    @14
    @20
    @15
    cD
    cF
    cV
    cW
    @7
    lkrsc.d
    @17
    lkrsc.v
    lkrsc.f
    lfl0f
    syl
    cD
    cF
    @10
    cL
    cV
    cW
    @7
    lkrsc.d
    @17
    lkrsc.v
    lkrsc.f
    lkrsc.l
    lkr0f
    syl2anc
    mpbiri
    eqtr2d
    sseqtrd
    adantr
    @8
    @5
    @12
    wceq
    wph
    @8
    @4
    @11
    cL
    @8
    @2
    @10
    cG
    @3
    @8
    @1
    @9
    cV
    cR
    @7
    sneq
    xpeq2d
    oveq2d
    fveq2d
    adantl
    sseqtr4d
    wph
    cR
    @7
    wne
    #
    wa
    #
    @5
    @0
    wceq
    @6
    @22
    cD
    cR
    c.x
    cF
    cG
    cK
    cL
    cV
    cW
    @7
    lkrsc.v
    lkrsc.d
    lkrsc.k
    lkrsc.t
    lkrsc.f
    lkrsc.l
    wph
    @13
    @21
    lkrsc.w
    adantr
    wph
    cG
    cF
    wcel
    @21
    lkrsc.g
    adantr
    wph
    cR
    cK
    wcel
    @21
    lkrsc.r
    adantr
    @17
    wph
    @21
    simpr
    lkrsc
    @0
    @5
    eqimss2
    syl
    pm2.61dane
end
