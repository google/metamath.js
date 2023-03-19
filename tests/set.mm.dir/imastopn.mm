include "cts.mm"
include "cfv.mm"
include "cqtop.mm"
include "co.mm"
include "ctopn.mm"
include "cbs.mm"
include "cpw.mm"
include "wss.mm"
include "wceq.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "wcel.mm"
include "crab.mm"
include "eqid.mm"
include "imastset.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wfn.mm"
include "wfo.mm"
include "fofn.mm"
include "syl.mm"
include "syl6eqel.mm"
include "fnex.mm"
include "syl2anc.mm"
include "qtopval.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "ssrab2.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "imasbas.mm"
include "syl5sseq.mm"
include "sspwb.mm"
include "sylib.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "topnid.mm"
include "syl6eqr.mm"
include "eqtr3d.mm"

theorem imastopn
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cJ: class J
  let cO: class O
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume imastps.u: |- ( ph -> U = ( F "s R ) )
  assume imastps.v: |- ( ph -> V = ( Base ` R ) )
  assume imastps.f: |- ( ph -> F : V -onto-> B )
  assume imastopn.r: |- ( ph -> R e. W )
  assume imastopn.j: |- J = ( TopOpen ` R )
  assume imastopn.o: |- O = ( TopOpen ` U )


  assert |- ( ph -> O = ( J qTop F ) )

  proof
    wph
    cU
    cts
    cfv
    #
    cO
    cJ
    cF
    cqtop
    co
    #
    wph
    @0
    cU
    ctopn
    cfv
    #
    cO
    wph
    @0
    cU
    cbs
    cfv
    #
    cpw
    #
    wss
    @0
    @2
    wceq
    wph
    @0
    cF
    ccnv
    vx
    cv
    cima
    cJ
    cuni
    #
    cin
    cJ
    wcel
    #
    vx
    cF
    @5
    cima
    #
    cpw
    #
    crab
    #
    @4
    wph
    @0
    @1
    @9
    wph
    cB
    cR
    cU
    cF
    cJ
    @0
    cV
    cW
    imastps.u
    imastps.v
    imastps.f
    imastopn.r
    imastopn.j
    @0
    eqid
    #
    imastset
    #
    wph
    cJ
    cvv
    wcel
    cF
    cvv
    wcel
    #
    @1
    @9
    wceq
    cJ
    cR
    ctopn
    cfv
    cvv
    imastopn.j
    cR
    ctopn
    fvex
    eqeltri
    wph
    cF
    cV
    wfn
    #
    cV
    cvv
    wcel
    @12
    wph
    cV
    cB
    cF
    wfo
    #
    @13
    imastps.f
    cV
    cB
    cF
    fofn
    syl
    wph
    cV
    cR
    cbs
    cfv
    cvv
    imastps.v
    cR
    cbs
    fvex
    syl6eqel
    cV
    cvv
    cF
    fnex
    syl2anc
    cF
    cJ
    cvv
    cvv
    @5
    vx
    @5
    eqid
    qtopval
    sylancr
    eqtrd
    wph
    @9
    @8
    @4
    @6
    vx
    @8
    ssrab2
    wph
    @7
    @3
    wss
    @8
    @4
    wss
    wph
    cF
    crn
    #
    @7
    @3
    cF
    @5
    imassrn
    wph
    @15
    cB
    @3
    wph
    @14
    @15
    cB
    wceq
    imastps.f
    cV
    cB
    cF
    forn
    syl
    wph
    cB
    cR
    cU
    cF
    cV
    cW
    imastps.u
    imastps.v
    imastps.f
    imastopn.r
    imasbas
    eqtrd
    syl5sseq
    @7
    @3
    sspwb
    sylib
    syl5ss
    eqsstrd
    @3
    @0
    cU
    @3
    eqid
    @10
    topnid
    syl
    imastopn.o
    syl6eqr
    @11
    eqtr3d
end
