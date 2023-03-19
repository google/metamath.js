include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "co.mm"
include "crg.mm"
include "frlmlmod.mm"
include "syl2anc.mm"
include "wss.mm"
include "eqid.mm"
include "frlmsslss2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "frlmsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "csupp.mm"
include "wf.mm"
include "uvcff.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "frlmbasf.mm"
include "cv.mm"
include "cdif.mm"
include "wa.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "disjdif.mm"
include "a1i.mm"
include "simpr.mm"
include "disjne.mm"
include "uvcvv0.mm"
include "suppss.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "lssvscl.mm"
include "syl22anc.mm"

theorem frlmssuvc1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume frlmssuvc1.f: |- F = ( R freeLMod I )
  assume frlmssuvc1.u: |- U = ( R unitVec I )
  assume frlmssuvc1.b: |- B = ( Base ` F )
  assume frlmssuvc1.k: |- K = ( Base ` R )
  assume frlmssuvc1.t: |- .x. = ( .s ` F )
  assume frlmssuvc1.z: |- .0. = ( 0g ` R )
  assume frlmssuvc1.c: |- C = { x e. B | ( x supp .0. ) C_ J }
  assume frlmssuvc1.r: |- ( ph -> R e. Ring )
  assume frlmssuvc1.i: |- ( ph -> I e. V )
  assume frlmssuvc1.j: |- ( ph -> J C_ I )
  assume frlmssuvc1.l: |- ( ph -> L e. J )
  assume frlmssuvc1.x: |- ( ph -> X e. K )

  disjoint B x
  disjoint F x
  disjoint I x
  disjoint J x
  disjoint K x
  disjoint L x
  disjoint R x
  disjoint .0. x
  disjoint ph x
  disjoint U x
  disjoint V x
  disjoint .x. x
  disjoint X x
  assert |- ( ph -> ( X .x. ( U ` L ) ) e. C )

  proof
    wph
    cF
    clmod
    wcel
    #
    cC
    cF
    clss
    cfv
    #
    wcel
    #
    cX
    cF
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    cL
    cU
    cfv
    #
    cC
    wcel
    #
    cX
    @5
    c.x
    co
    cC
    wcel
    wph
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    @0
    frlmssuvc1.r
    frlmssuvc1.i
    cR
    cF
    cI
    cV
    frlmssuvc1.f
    frlmlmod
    syl2anc
    wph
    @7
    @8
    cJ
    cI
    wss
    @2
    frlmssuvc1.r
    frlmssuvc1.i
    frlmssuvc1.j
    vx
    cB
    cC
    cR
    @1
    cI
    cJ
    cV
    cF
    c.0
    frlmssuvc1.f
    @1
    eqid
    #
    frlmssuvc1.b
    frlmssuvc1.z
    frlmssuvc1.c
    frlmsslss2
    syl3anc
    wph
    cX
    cK
    @4
    frlmssuvc1.x
    wph
    cK
    cR
    cbs
    cfv
    @4
    frlmssuvc1.k
    wph
    cR
    @3
    cbs
    wph
    @7
    @8
    cR
    @3
    wceq
    frlmssuvc1.r
    frlmssuvc1.i
    cR
    cF
    cI
    crg
    cV
    frlmssuvc1.f
    frlmsca
    syl2anc
    fveq2d
    syl5eq
    eleqtrd
    wph
    @5
    cB
    wcel
    #
    @5
    c.0
    csupp
    co
    #
    cJ
    wss
    #
    @6
    wph
    cI
    cB
    cL
    cU
    wph
    @7
    @8
    cI
    cB
    cU
    wf
    frlmssuvc1.r
    frlmssuvc1.i
    cB
    cR
    cU
    cI
    cV
    cF
    frlmssuvc1.u
    frlmssuvc1.f
    frlmssuvc1.b
    uvcff
    syl2anc
    wph
    cJ
    cI
    cL
    frlmssuvc1.j
    frlmssuvc1.l
    sseldd
    #
    ffvelrnd
    #
    wph
    cI
    cK
    vx
    @5
    cJ
    c.0
    wph
    @8
    @10
    cI
    cK
    @5
    wf
    frlmssuvc1.i
    @14
    cB
    cR
    cF
    cI
    cK
    cV
    @5
    frlmssuvc1.f
    frlmssuvc1.k
    frlmssuvc1.b
    frlmbasf
    syl2anc
    wph
    vx
    cv
    #
    cI
    cJ
    cdif
    #
    wcel
    #
    wa
    #
    cR
    cU
    cI
    cL
    @15
    crg
    cV
    c.0
    frlmssuvc1.u
    wph
    @7
    @17
    frlmssuvc1.r
    adantr
    wph
    @8
    @17
    frlmssuvc1.i
    adantr
    wph
    cL
    cI
    wcel
    @17
    @13
    adantr
    @17
    @15
    cI
    wcel
    wph
    @15
    cI
    cJ
    eldifi
    adantl
    @18
    cJ
    @16
    cin
    c0
    wceq
    #
    cL
    cJ
    wcel
    #
    @17
    cL
    @15
    wne
    @19
    @18
    cJ
    cI
    disjdif
    a1i
    wph
    @20
    @17
    frlmssuvc1.l
    adantr
    wph
    @17
    simpr
    cJ
    @16
    cL
    @15
    disjne
    syl3anc
    frlmssuvc1.z
    uvcvv0
    suppss
    @15
    c.0
    csupp
    co
    #
    cJ
    wss
    @12
    vx
    @5
    cB
    cC
    @15
    @5
    wceq
    @21
    @11
    cJ
    @15
    @5
    c.0
    csupp
    oveq1
    sseq1d
    frlmssuvc1.c
    elrab2
    sylanbrc
    @4
    @1
    c.x
    cC
    @3
    cF
    cX
    @5
    @3
    eqid
    frlmssuvc1.t
    @4
    eqid
    @9
    lssvscl
    syl22anc
end
