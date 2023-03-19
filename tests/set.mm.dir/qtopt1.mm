include "cqtop.mm"
include "co.mm"
include "ctop.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "wral.mm"
include "ct1.mm"
include "wfn.mm"
include "t1top.mm"
include "syl.mm"
include "wfo.mm"
include "fofn.mm"
include "qtoptop.mm"
include "syl2anc.mm"
include "wa.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "simpr.mm"
include "wceq.mm"
include "qtopuni.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "snssd.mm"
include "syldan.mm"
include "wb.mm"
include "ctopon.mm"
include "jctir.mm"
include "istopon.mm"
include "sylibr.mm"
include "qtopcld.mm"
include "mpbir2and.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "ist1.mm"
include "sylanbrc.mm"

theorem qtopt1
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume qtopt1.x: |- X = U. J
  assume qtopt1.1: |- ( ph -> J e. Fre )
  assume qtopt1.2: |- ( ph -> F : X -onto-> Y )
  assume qtopt1.3: |- ( ( ph /\ x e. Y ) -> ( `' F " { x } ) e. ( Clsd ` J ) )

  disjoint F x
  disjoint J x
  disjoint ph x
  assert |- ( ph -> ( J qTop F ) e. Fre )

  proof
    wph
    cJ
    cF
    cqtop
    co
    #
    ctop
    wcel
    #
    vx
    cv
    #
    csn
    #
    @0
    ccld
    cfv
    wcel
    #
    vx
    @0
    cuni
    #
    wral
    @0
    ct1
    wcel
    wph
    cJ
    ctop
    wcel
    #
    cF
    cX
    wfn
    #
    @1
    wph
    cJ
    ct1
    wcel
    @6
    qtopt1.1
    cJ
    t1top
    syl
    #
    wph
    cX
    cY
    cF
    wfo
    #
    @7
    qtopt1.2
    cX
    cY
    cF
    fofn
    syl
    cF
    cJ
    cX
    qtopt1.x
    qtoptop
    syl2anc
    wph
    @4
    vx
    @5
    wph
    @2
    @5
    wcel
    #
    wa
    #
    @4
    @3
    cY
    wss
    #
    cF
    ccnv
    @3
    cima
    cJ
    ccld
    cfv
    wcel
    #
    @11
    @2
    cY
    @11
    @2
    @5
    cY
    wph
    @10
    simpr
    wph
    cY
    @5
    wceq
    #
    @10
    wph
    @6
    @9
    @14
    @8
    qtopt1.2
    cF
    cJ
    cX
    cY
    qtopt1.x
    qtopuni
    syl2anc
    adantr
    eleqtrrd
    #
    snssd
    wph
    @10
    @2
    cY
    wcel
    @13
    @15
    qtopt1.3
    syldan
    wph
    @4
    @12
    @13
    wa
    wb
    #
    @10
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @9
    @16
    wph
    @6
    cX
    cJ
    cuni
    wceq
    #
    wa
    @17
    wph
    @6
    @18
    @8
    qtopt1.x
    jctir
    cX
    cJ
    istopon
    sylibr
    qtopt1.2
    @3
    cF
    cJ
    cX
    cY
    qtopcld
    syl2anc
    adantr
    mpbir2and
    ralrimiva
    @0
    @5
    vx
    @5
    eqid
    ist1
    sylanbrc
end
