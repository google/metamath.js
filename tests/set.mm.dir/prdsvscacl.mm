include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "crg.mm"
include "clmod.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "prdsvscaval.mm"
include "wcel.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "csca.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "prdsbasmpt.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem prdsvscacl
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cW: class W
  let cY: class Y
  assume prdsvscacl.y: |- Y = ( S Xs_ R )
  assume prdsvscacl.b: |- B = ( Base ` Y )
  assume prdsvscacl.t: |- .x. = ( .s ` Y )
  assume prdsvscacl.k: |- K = ( Base ` S )
  assume prdsvscacl.s: |- ( ph -> S e. Ring )
  assume prdsvscacl.i: |- ( ph -> I e. W )
  assume prdsvscacl.r: |- ( ph -> R : I --> LMod )
  assume prdsvscacl.f: |- ( ph -> F e. K )
  assume prdsvscacl.g: |- ( ph -> G e. B )
  assume prdsvscacl.sr: |- ( ( ph /\ x e. I ) -> ( Scalar ` ( R ` x ) ) = S )

  disjoint B x
  disjoint F x
  disjoint G x
  disjoint I x
  disjoint K x
  disjoint R x
  disjoint S x
  disjoint ph x
  disjoint W x
  disjoint Y x
  assert |- ( ph -> ( F .x. G ) e. B )

  proof
    wph
    cF
    cG
    c.x
    co
    vx
    cI
    cF
    vx
    cv
    #
    cG
    cfv
    #
    @0
    cR
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cB
    wph
    vx
    cB
    cR
    cS
    c.x
    cF
    cG
    cI
    cK
    crg
    cW
    cY
    prdsvscacl.y
    prdsvscacl.b
    prdsvscacl.t
    prdsvscacl.k
    prdsvscacl.s
    prdsvscacl.i
    wph
    cI
    clmod
    cR
    wf
    cR
    cI
    wfn
    #
    prdsvscacl.r
    cI
    clmod
    cR
    ffn
    syl
    #
    prdsvscacl.f
    prdsvscacl.g
    prdsvscaval
    wph
    @5
    cB
    wcel
    @4
    @2
    cbs
    cfv
    #
    wcel
    #
    vx
    cI
    wral
    wph
    @9
    vx
    cI
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @2
    clmod
    wcel
    cF
    @2
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @1
    @8
    wcel
    @9
    wph
    cI
    clmod
    @0
    cR
    prdsvscacl.r
    ffvelrnda
    @11
    cF
    cK
    @13
    wph
    cF
    cK
    wcel
    @10
    prdsvscacl.f
    adantr
    @11
    @13
    cS
    cbs
    cfv
    cK
    @11
    @12
    cS
    cbs
    prdsvscacl.sr
    fveq2d
    prdsvscacl.k
    syl6eqr
    eleqtrrd
    @11
    cB
    cR
    cS
    cG
    cI
    @0
    crg
    cW
    cY
    prdsvscacl.y
    prdsvscacl.b
    wph
    cS
    crg
    wcel
    @10
    prdsvscacl.s
    adantr
    wph
    cI
    cW
    wcel
    @10
    prdsvscacl.i
    adantr
    wph
    @6
    @10
    @7
    adantr
    wph
    cG
    cB
    wcel
    @10
    prdsvscacl.g
    adantr
    wph
    @10
    simpr
    prdsbasprj
    cF
    @3
    @12
    @13
    @8
    @2
    @1
    @8
    eqid
    @12
    eqid
    @3
    eqid
    @13
    eqid
    lmodvscl
    syl3anc
    ralrimiva
    wph
    vx
    cB
    cR
    cS
    @4
    cI
    crg
    cW
    cY
    prdsvscacl.y
    prdsvscacl.b
    prdsvscacl.s
    prdsvscacl.i
    @7
    prdsbasmpt
    mpbird
    eqeltrd
end
