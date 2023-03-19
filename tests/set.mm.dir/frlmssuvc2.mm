include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "csupp.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "crab.mm"
include "wn.mm"
include "eldifad.mm"
include "cmulr.mm"
include "cur.mm"
include "csn.mm"
include "crg.mm"
include "wf.mm"
include "uvcff.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "frlmvscaval.mm"
include "uvcvv1.mm"
include "oveq2d.mm"
include "wceq.mm"
include "ringridm.mm"
include "3eqtrd.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "eldifbd.mm"
include "nelss.mm"
include "wfn.mm"
include "cvv.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "frlmlmod.mm"
include "frlmsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "frlmbasf.mm"
include "ffn.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "suppvalfn.mm"
include "sseq1d.mm"
include "mtbird.mm"
include "intnand.mm"
include "oveq1.mm"
include "elrab2.mm"
include "sylnibr.mm"

theorem frlmssuvc2
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
  assume frlmssuvc2.l: |- ( ph -> L e. ( I \ J ) )
  assume frlmssuvc2.x: |- ( ph -> X e. ( K \ { .0. } ) )

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
  assert |- ( ph -> -. ( X .x. ( U ` L ) ) e. C )

  proof
    wph
    cX
    cL
    cU
    cfv
    #
    c.x
    co
    #
    cB
    wcel
    #
    @1
    c.0
    csupp
    co
    #
    cJ
    wss
    #
    wa
    @1
    cC
    wcel
    wph
    @4
    @2
    wph
    @4
    vx
    cv
    #
    @1
    cfv
    #
    c.0
    wne
    #
    vx
    cI
    crab
    #
    cJ
    wss
    #
    wph
    cL
    @8
    wcel
    #
    cL
    cJ
    wcel
    wn
    @9
    wn
    wph
    cL
    cI
    wcel
    cL
    @1
    cfv
    #
    c.0
    wne
    #
    @10
    wph
    cL
    cI
    cJ
    frlmssuvc2.l
    eldifad
    #
    wph
    @11
    cX
    c.0
    wph
    @11
    cX
    cL
    @0
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    cX
    cR
    cur
    cfv
    #
    @15
    co
    #
    cX
    wph
    cX
    cB
    cR
    c.x
    @15
    cI
    cL
    cK
    cV
    @0
    cF
    frlmssuvc1.f
    frlmssuvc1.b
    frlmssuvc1.k
    frlmssuvc1.i
    wph
    cX
    cK
    c.0
    csn
    #
    frlmssuvc2.x
    eldifad
    #
    wph
    cI
    cB
    cL
    cU
    wph
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
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
    @13
    ffvelrnd
    #
    @13
    frlmssuvc1.t
    @15
    eqid
    #
    frlmvscaval
    wph
    @14
    @16
    cX
    @15
    wph
    cR
    cU
    @16
    cI
    cL
    crg
    cV
    frlmssuvc1.u
    frlmssuvc1.r
    frlmssuvc1.i
    @13
    @16
    eqid
    #
    uvcvv1
    oveq2d
    wph
    @20
    cX
    cK
    wcel
    @17
    cX
    wceq
    frlmssuvc1.r
    @19
    cK
    cR
    @15
    @16
    cX
    frlmssuvc1.k
    @23
    @24
    ringridm
    syl2anc
    3eqtrd
    wph
    cX
    cK
    @18
    cdif
    wcel
    cX
    c.0
    wne
    frlmssuvc2.x
    cX
    cK
    c.0
    eldifsni
    syl
    eqnetrd
    @7
    @12
    vx
    cL
    cI
    @5
    cL
    wceq
    @6
    @11
    c.0
    @5
    cL
    @1
    fveq2
    neeq1d
    elrab
    sylanbrc
    wph
    cL
    cI
    cJ
    frlmssuvc2.l
    eldifbd
    cL
    @8
    cJ
    nelss
    syl2anc
    wph
    @3
    @8
    cJ
    wph
    @1
    cI
    wfn
    #
    @21
    c.0
    cvv
    wcel
    #
    @3
    @8
    wceq
    wph
    cI
    cK
    @1
    wf
    #
    @25
    wph
    @21
    @2
    @27
    frlmssuvc1.i
    wph
    cF
    clmod
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
    @0
    cB
    wcel
    @2
    wph
    @20
    @21
    @28
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
    cX
    cK
    @30
    @19
    wph
    cK
    cR
    cbs
    cfv
    @30
    frlmssuvc1.k
    wph
    cR
    @29
    cbs
    wph
    @20
    @21
    cR
    @29
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
    @22
    cX
    c.x
    @29
    @30
    cB
    cF
    @0
    frlmssuvc1.b
    @29
    eqid
    frlmssuvc1.t
    @30
    eqid
    lmodvscl
    syl3anc
    cB
    cR
    cF
    cI
    cK
    cV
    @1
    frlmssuvc1.f
    frlmssuvc1.k
    frlmssuvc1.b
    frlmbasf
    syl2anc
    cI
    cK
    @1
    ffn
    syl
    frlmssuvc1.i
    @26
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    frlmssuvc1.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    vx
    @1
    cV
    cvv
    cI
    c.0
    suppvalfn
    syl3anc
    sseq1d
    mtbird
    intnand
    @5
    c.0
    csupp
    co
    #
    cJ
    wss
    @4
    vx
    @1
    cB
    cC
    @5
    @1
    wceq
    @31
    @3
    cJ
    @5
    @1
    c.0
    csupp
    oveq1
    sseq1d
    frlmssuvc1.c
    elrab2
    sylnibr
end
