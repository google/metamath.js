include "ccom.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wceq.mm"
include "wfun.mm"
include "wf1.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "syl.mm"
include "cofunex2g.mm"
include "syl2anc.mm"
include "suppimacnv.mm"
include "fsuppimpd.mm"
include "eqeltrrd.mm"
include "fsuppcolem.mm"
include "eqeltrd.mm"
include "wb.mm"
include "fsuppimp.mm"
include "simpld.mm"
include "f1fun.mm"
include "funco.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem fsuppco
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume fsuppco.f: |- ( ph -> F finSupp Z )
  assume fsuppco.g: |- ( ph -> G : X -1-1-> Y )
  assume fsuppco.z: |- ( ph -> Z e. W )
  assume fsuppco.v: |- ( ph -> F e. V )


  assert |- ( ph -> ( F o. G ) finSupp Z )

  proof
    wph
    cF
    cG
    ccom
    #
    cZ
    cfsupp
    wbr
    #
    @0
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    @2
    @0
    ccnv
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cfn
    wph
    @0
    cvv
    wcel
    #
    cZ
    cW
    wcel
    #
    @2
    @5
    wceq
    wph
    cF
    cV
    wcel
    #
    cG
    ccnv
    wfun
    #
    @6
    fsuppco.v
    wph
    cX
    cY
    cG
    wf1
    #
    @9
    fsuppco.g
    @10
    cX
    cY
    cG
    wf
    @9
    cX
    cY
    cG
    df-f1
    simprbi
    syl
    cF
    cG
    cV
    cofunex2g
    syl2anc
    #
    fsuppco.z
    @0
    cvv
    cW
    cZ
    suppimacnv
    syl2anc
    wph
    cF
    cG
    cX
    cY
    cZ
    wph
    cF
    cZ
    csupp
    co
    #
    cF
    ccnv
    @4
    cima
    #
    cfn
    wph
    @8
    @7
    @12
    @13
    wceq
    fsuppco.v
    fsuppco.z
    cF
    cV
    cW
    cZ
    suppimacnv
    syl2anc
    wph
    cF
    cZ
    fsuppco.f
    fsuppimpd
    eqeltrrd
    fsuppco.g
    fsuppcolem
    eqeltrd
    wph
    @0
    wfun
    #
    @6
    @7
    @1
    @3
    wb
    wph
    cF
    wfun
    #
    cG
    wfun
    #
    @14
    wph
    cF
    cZ
    cfsupp
    wbr
    #
    @15
    fsuppco.f
    @17
    @15
    @12
    cfn
    wcel
    cF
    cZ
    fsuppimp
    simpld
    syl
    wph
    @10
    @16
    fsuppco.g
    cX
    cY
    cG
    f1fun
    syl
    cF
    cG
    funco
    syl2anc
    @11
    fsuppco.z
    @0
    cvv
    cW
    cZ
    funisfsupp
    syl3anc
    mpbird
end
