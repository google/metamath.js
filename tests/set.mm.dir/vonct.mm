include "cvoln.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cc0.mm"
include "wceq.mm"
include "iunid.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cdm.mm"
include "nfv.mm"
include "vonmea.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "adantr.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "sselda.mm"
include "snvonmbl.mm"
include "wdisj.mm"
include "sndisj.mm"
include "meadjiun.mm"
include "vonsn.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "dmmeasal.mm"
include "saliuncl.mm"
include "syl5eqelr.mm"
include "sge0z.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem vonct
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume vonct.1: |- ( ph -> X e. Fin )
  assume vonct.2: |- ( ph -> A C_ ( RR ^m X ) )
  assume vonct.3: |- ( ph -> A ~<_ _om )


  assert |- ( ph -> ( ( voln ` X ) ` A ) = 0 )

  proof
    wph
    cA
    cX
    cvoln
    cfv
    #
    cfv
    #
    vx
    cA
    vx
    cv
    #
    csn
    #
    ciun
    #
    @0
    cfv
    #
    vx
    cA
    @3
    @0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cc0
    @1
    @5
    wceq
    wph
    cA
    @4
    @0
    @4
    cA
    vx
    cA
    iunid
    #
    eqcomi
    fveq2i
    a1i
    wph
    cA
    @3
    @0
    cdm
    #
    vx
    @0
    wph
    vx
    nfv
    #
    wph
    cX
    vonct.1
    vonmea
    #
    @10
    eqid
    #
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @2
    cX
    wph
    cX
    cfn
    wcel
    @14
    vonct.1
    adantr
    #
    wph
    cA
    cr
    cX
    cmap
    co
    @2
    vonct.2
    sselda
    #
    snvonmbl
    #
    vonct.3
    vx
    cA
    @3
    wdisj
    wph
    vx
    cA
    sndisj
    a1i
    meadjiun
    wph
    @8
    vx
    cA
    cc0
    cmpt
    #
    csumge0
    cfv
    cc0
    wph
    @7
    @19
    csumge0
    wph
    vx
    cA
    @6
    cc0
    @15
    @2
    cX
    @16
    @17
    vonsn
    mpteq2dva
    fveq2d
    wph
    cA
    vx
    @10
    @11
    wph
    cA
    @4
    @10
    @9
    wph
    @10
    vx
    @3
    cA
    wph
    @10
    @0
    @12
    @13
    dmmeasal
    vonct.3
    @18
    saliuncl
    syl5eqelr
    sge0z
    eqtrd
    3eqtrd
end
