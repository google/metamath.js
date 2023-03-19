include "wfn.mm"
include "ccnv.mm"
include "wceq.mm"
include "wf1o.mm"
include "wf.mm"
include "lmif.mm"
include "ffn.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "crn.mm"
include "simpr.mm"
include "lmilmi.mm"
include "ralrimiva.mm"
include "nvocnv.mm"
include "syl2anc.mm"
include "nvof1o.mm"

theorem lmif1o
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )


  assert |- ( ph -> M : P -1-1-onto-> P )

  proof
    wph
    cM
    cP
    wfn
    #
    cM
    ccnv
    cM
    wceq
    #
    cP
    cP
    cM
    wf1o
    wph
    cP
    cP
    cM
    wf
    #
    @0
    wph
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmif
    #
    cP
    cP
    cM
    ffn
    syl
    wph
    @2
    vb
    cv
    #
    cM
    cfv
    cM
    cfv
    @4
    wceq
    #
    vb
    cP
    wral
    @1
    @3
    wph
    @5
    vb
    cP
    wph
    @4
    cP
    wcel
    #
    wa
    @4
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    wph
    cG
    cstrkg
    wcel
    @6
    ismid.g
    adantr
    wph
    cG
    c2
    cstrkgld
    wbr
    @6
    ismid.1
    adantr
    lmif.m
    lmif.l
    wph
    cD
    cL
    crn
    wcel
    @6
    lmif.d
    adantr
    wph
    @6
    simpr
    lmilmi
    ralrimiva
    vb
    cP
    cM
    nvocnv
    syl2anc
    cP
    cM
    nvof1o
    syl2anc
end
