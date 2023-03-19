include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csumge0.mm"
include "cle.mm"
include "wss.mm"
include "wcel.mm"
include "wbr.mm"
include "cr.mm"
include "sge0rnre.mm"
include "ressxr.mm"
include "a1i.mm"
include "sstrd.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "elind.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sumex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "supxrub.mm"
include "sge0reval.mm"
include "eqcomd.mm"
include "breqtrd.mm"

theorem fsumlesge0
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume fsumlesge0.x: |- ( ph -> X e. V )
  assume fsumlesge0.f: |- ( ph -> F : X --> ( 0 [,) +oo ) )
  assume fsumlesge0.y: |- ( ph -> Y C_ X )
  assume fsumlesge0.fi: |- ( ph -> Y e. Fin )

  disjoint F x
  disjoint Y x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> sum_ x e. Y ( F ` x ) <_ ( sum^ ` F ) )

  proof
    wph
    cY
    vx
    cv
    #
    cF
    cfv
    #
    vx
    csu
    #
    vy
    cX
    cpw
    #
    cfn
    cin
    #
    vy
    cv
    #
    vz
    cv
    #
    cF
    cfv
    #
    vz
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cF
    csumge0
    cfv
    #
    cle
    wph
    @10
    cxr
    wss
    @2
    @10
    wcel
    #
    @2
    @11
    cle
    wbr
    wph
    @10
    cr
    cxr
    wph
    vy
    vz
    cF
    cX
    fsumlesge0.f
    sge0rnre
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    wph
    @13
    @2
    @8
    wceq
    #
    vy
    @4
    wrex
    #
    wph
    cY
    @4
    wcel
    @2
    cY
    @7
    vz
    csu
    #
    wceq
    #
    @15
    wph
    @3
    cfn
    cY
    wph
    cY
    @3
    wcel
    #
    cY
    cX
    wss
    #
    fsumlesge0.y
    wph
    cY
    cvv
    wcel
    @18
    @19
    wb
    wph
    cY
    cX
    cV
    fsumlesge0.x
    fsumlesge0.y
    ssexd
    cY
    cX
    cvv
    elpwg
    syl
    mpbird
    fsumlesge0.fi
    elind
    @17
    wph
    cY
    @1
    @7
    vx
    vz
    @0
    @6
    cF
    fveq2
    cbvsumv
    a1i
    @14
    @17
    vy
    cY
    @4
    @5
    cY
    wceq
    @8
    @16
    @2
    @5
    cY
    @7
    vz
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    wph
    @2
    cvv
    wcel
    #
    @13
    @15
    wb
    @20
    wph
    cY
    @1
    vx
    sumex
    a1i
    vy
    @4
    @8
    @2
    @9
    cvv
    @9
    eqid
    elrnmpt
    syl
    mpbird
    @10
    @2
    supxrub
    syl2anc
    wph
    @12
    @11
    wph
    vy
    vz
    cF
    cV
    cX
    fsumlesge0.x
    fsumlesge0.f
    sge0reval
    eqcomd
    breqtrd
end
