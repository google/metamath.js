include "cmap.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "ces.mm"
include "cfv.mm"
include "crn.mm"
include "cress.mm"
include "cmpl.mm"
include "cascl.mm"
include "eqid.mm"
include "evlssca.mm"
include "cbs.mm"
include "wfn.mm"
include "wcel.mm"
include "cpws.mm"
include "crh.mm"
include "wf.mm"
include "ccrg.mm"
include "csubrg.mm"
include "evlsrhm.mm"
include "syl3anc.mm"
include "rhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "csca.mm"
include "crg.mm"
include "subrgring.mm"
include "syl.mm"
include "wa.mm"
include "mplring.mm"
include "mpllmod.mm"
include "asclf.mm"
include "syl2anc.mm"
include "wss.mm"
include "wceq.mm"
include "subrgss.mm"
include "ressbas2.mm"
include "cvv.mm"
include "ovexd.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "syl6eleqr.mm"

theorem mpfconst
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cX: class X
  assume mpfconst.b: |- B = ( Base ` S )
  assume mpfconst.q: |- Q = ran ( ( I evalSub S ) ` R )
  assume mpfconst.i: |- ( ph -> I e. V )
  assume mpfconst.s: |- ( ph -> S e. CRing )
  assume mpfconst.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume mpfconst.x: |- ( ph -> X e. R )


  assert |- ( ph -> ( ( B ^m I ) X. { X } ) e. Q )

  proof
    wph
    cB
    cI
    cmap
    co
    #
    cX
    csn
    cxp
    #
    cR
    cI
    cS
    ces
    co
    cfv
    #
    crn
    #
    cQ
    wph
    cX
    cI
    cS
    cR
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    cfv
    #
    @2
    cfv
    #
    @1
    @3
    wph
    @6
    cB
    @2
    cR
    cS
    @4
    cI
    cV
    @5
    cX
    @2
    eqid
    #
    @5
    eqid
    #
    @4
    eqid
    #
    mpfconst.b
    @6
    eqid
    #
    mpfconst.i
    mpfconst.s
    mpfconst.r
    mpfconst.x
    evlssca
    wph
    @2
    @5
    cbs
    cfv
    #
    wfn
    #
    @7
    @13
    wcel
    @8
    @3
    wcel
    wph
    @2
    @5
    cS
    @0
    cpws
    co
    #
    crh
    co
    wcel
    #
    @13
    @15
    cbs
    cfv
    #
    @2
    wf
    @14
    wph
    cI
    cV
    wcel
    #
    cS
    ccrg
    wcel
    cR
    cS
    csubrg
    cfv
    wcel
    #
    @16
    mpfconst.i
    mpfconst.s
    mpfconst.r
    cB
    @2
    cR
    cS
    @15
    @4
    cI
    cV
    @5
    @9
    @10
    @11
    @15
    eqid
    mpfconst.b
    evlsrhm
    syl3anc
    @13
    @17
    @5
    @15
    @2
    @13
    eqid
    #
    @17
    eqid
    rhmf
    @13
    @17
    @2
    ffn
    3syl
    wph
    @5
    csca
    cfv
    #
    cbs
    cfv
    #
    @13
    cX
    @6
    wph
    @18
    @4
    crg
    wcel
    #
    @22
    @13
    @6
    wf
    mpfconst.i
    wph
    @19
    @23
    mpfconst.r
    cR
    cS
    @4
    @11
    subrgring
    syl
    @18
    @23
    wa
    @6
    @13
    @21
    @22
    @5
    @12
    @21
    eqid
    @5
    @4
    cI
    cV
    @10
    mplring
    @5
    @4
    cI
    cV
    @10
    mpllmod
    @22
    eqid
    @20
    asclf
    syl2anc
    wph
    cX
    cR
    @22
    mpfconst.x
    wph
    cR
    @4
    cbs
    cfv
    #
    @22
    wph
    @19
    cR
    cB
    wss
    cR
    @24
    wceq
    mpfconst.r
    cR
    cB
    cS
    mpfconst.b
    subrgss
    cR
    cB
    @4
    cS
    @11
    mpfconst.b
    ressbas2
    3syl
    wph
    @4
    @21
    cbs
    wph
    @5
    @4
    cI
    cV
    cvv
    @10
    mpfconst.i
    wph
    cS
    cR
    cress
    ovexd
    mplsca
    fveq2d
    eqtrd
    eleqtrd
    ffvelrnd
    @13
    @7
    @2
    fnfvelrn
    syl2anc
    eqeltrrd
    mpfconst.q
    syl6eleqr
end
