include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "fmptdf.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "nfan.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "pimconstlt1.mm"
include "eqidd.mm"
include "wceq.mm"
include "wss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "csalg.mm"
include "cvv.mm"
include "uniexd.mm"
include "ssexd.mm"
include "salunid.mm"
include "eqid.mm"
include "elrestd.mm"
include "eqeltrd.mm"
include "wn.mm"
include "c0.mm"
include "cxr.mm"
include "rexr.mm"
include "ad2antlr.mm"
include "cle.mm"
include "simplr.mm"
include "lenltd.mm"
include "mpbird.mm"
include "pimconstlt0.mm"
include "subsalsal.mm"
include "0sald.mm"
include "pm2.61dan.mm"
include "issmfdf.mm"

theorem smfconst
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume smfconst.x: |- F/ x ph
  assume smfconst.s: |- ( ph -> S e. SAlg )
  assume smfconst.a: |- ( ph -> A C_ U. S )
  assume smfconst.b: |- ( ph -> B e. RR )
  assume smfconst.f: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint B x
  disjoint F a
  disjoint S a
  disjoint a ph
  disjoint a x
  disjoint k x
  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cS
    cF
    va
    vx
    cF
    vx
    cA
    cB
    cmpt
    smfconst.f
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    wph
    va
    nfv
    smfconst.s
    smfconst.a
    wph
    vx
    cA
    cB
    cr
    cF
    smfconst.x
    wph
    cB
    cr
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    smfconst.b
    adantr
    smfconst.f
    fmptdf
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    cB
    @2
    clt
    wbr
    #
    @1
    cF
    cfv
    @2
    clt
    wbr
    vx
    cA
    crab
    #
    cS
    cA
    crest
    co
    #
    wcel
    @4
    @5
    wa
    #
    @6
    cS
    cuni
    #
    cA
    cin
    #
    @7
    @8
    @6
    cA
    cA
    @10
    @8
    vx
    cA
    cB
    @2
    cF
    @4
    @5
    vx
    wph
    @3
    vx
    smfconst.x
    @3
    vx
    nfv
    nfan
    #
    @5
    vx
    nfv
    nfan
    wph
    @0
    @3
    @5
    smfconst.b
    ad2antrr
    smfconst.f
    @4
    @5
    simpr
    pimconstlt1
    @8
    cA
    eqidd
    wph
    cA
    @10
    wceq
    @3
    @5
    wph
    @10
    cA
    wph
    cA
    @9
    wss
    @10
    cA
    wceq
    smfconst.a
    cA
    @9
    sseqin2
    sylib
    eqcomd
    ad2antrr
    3eqtrd
    @8
    @10
    cA
    cS
    csalg
    cvv
    @9
    wph
    cS
    csalg
    wcel
    @3
    @5
    smfconst.s
    ad2antrr
    #
    wph
    cA
    cvv
    wcel
    @3
    @5
    wph
    cA
    @9
    cvv
    wph
    cS
    csalg
    smfconst.s
    uniexd
    smfconst.a
    ssexd
    #
    ad2antrr
    @8
    cS
    @12
    salunid
    @10
    eqid
    elrestd
    eqeltrd
    @4
    @5
    wn
    #
    wa
    #
    @6
    c0
    @7
    @15
    vx
    cA
    cB
    @2
    cF
    @4
    @14
    vx
    @11
    @14
    vx
    nfv
    nfan
    wph
    @0
    @3
    @14
    smfconst.b
    ad2antrr
    #
    smfconst.f
    @3
    @2
    cxr
    wcel
    wph
    @14
    @2
    rexr
    ad2antlr
    @15
    @2
    cB
    cle
    wbr
    @14
    @4
    @14
    simpr
    @15
    @2
    cB
    wph
    @3
    @14
    simplr
    @16
    lenltd
    mpbird
    pimconstlt0
    wph
    c0
    @7
    wcel
    @3
    @14
    wph
    @7
    wph
    cA
    cS
    @7
    cvv
    smfconst.s
    @13
    @7
    eqid
    subsalsal
    0sald
    ad2antrr
    eqeltrd
    pm2.61dan
    issmfdf
end
