include "cress.mm"
include "co.mm"
include "cmvr.mm"
include "cfv.mm"
include "ces.mm"
include "cmap.mm"
include "cv.mm"
include "cmpt.mm"
include "eqid.mm"
include "evlsvar.mm"
include "crn.mm"
include "cmpl.mm"
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
include "crg.mm"
include "subrgring.mm"
include "syl.mm"
include "mvrcl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"

theorem mpfproj
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cJ: class J
  let cV: class V
  assume mpfconst.b: |- B = ( Base ` S )
  assume mpfconst.q: |- Q = ran ( ( I evalSub S ) ` R )
  assume mpfconst.i: |- ( ph -> I e. V )
  assume mpfconst.s: |- ( ph -> S e. CRing )
  assume mpfconst.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume mpfproj.j: |- ( ph -> J e. I )

  disjoint B f
  disjoint I f
  disjoint J f
  disjoint R f
  disjoint S f
  disjoint V f
  assert |- ( ph -> ( f e. ( B ^m I ) |-> ( f ` J ) ) e. Q )

  proof
    wph
    cJ
    cI
    cS
    cR
    cress
    co
    #
    cmvr
    co
    #
    cfv
    #
    cR
    cI
    cS
    ces
    co
    cfv
    #
    cfv
    #
    vf
    cB
    cI
    cmap
    co
    #
    cJ
    vf
    cv
    cfv
    cmpt
    cQ
    wph
    cB
    @3
    cR
    cS
    @0
    vf
    cI
    @1
    cV
    cJ
    @3
    eqid
    #
    @1
    eqid
    #
    @0
    eqid
    #
    mpfconst.b
    mpfconst.i
    mpfconst.s
    mpfconst.r
    mpfproj.j
    evlsvar
    wph
    @4
    @3
    crn
    #
    cQ
    wph
    @3
    cI
    @0
    cmpl
    co
    #
    cbs
    cfv
    #
    wfn
    #
    @2
    @11
    wcel
    @4
    @9
    wcel
    wph
    @3
    @10
    cS
    @5
    cpws
    co
    #
    crh
    co
    wcel
    #
    @11
    @13
    cbs
    cfv
    #
    @3
    wf
    @12
    wph
    cI
    cV
    wcel
    cS
    ccrg
    wcel
    cR
    cS
    csubrg
    cfv
    wcel
    #
    @14
    mpfconst.i
    mpfconst.s
    mpfconst.r
    cB
    @3
    cR
    cS
    @13
    @0
    cI
    cV
    @10
    @6
    @10
    eqid
    #
    @8
    @13
    eqid
    mpfconst.b
    evlsrhm
    syl3anc
    @11
    @15
    @10
    @13
    @3
    @11
    eqid
    #
    @15
    eqid
    rhmf
    @11
    @15
    @3
    ffn
    3syl
    wph
    @11
    @10
    @0
    cI
    @1
    cV
    cJ
    @17
    @7
    @18
    mpfconst.i
    wph
    @16
    @0
    crg
    wcel
    mpfconst.r
    cR
    cS
    @0
    @8
    subrgring
    syl
    mpfproj.j
    mvrcl
    @11
    @2
    @3
    fnfvelrn
    syl2anc
    mpfconst.q
    syl6eleqr
    eqeltrrd
end
