include "com.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "cwdom.mm"
include "wbr.mm"
include "wpss.mm"
include "crab.mm"
include "cin.mm"
include "cen.mm"
include "crio.mm"
include "cmpt.mm"
include "cdif.mm"
include "ccom.mm"
include "wa.mm"
include "cio.mm"
include "simp1.mm"
include "weq.mm"
include "suceq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "psseq12d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "isf32lem10.mm"
include "impcom.mm"

theorem isf32lem11
  let cF: class F
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vl: setvar l
  let va: setvar a
  let vx: setvar x

  disjoint F b
  disjoint G b
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b l
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c l
  disjoint F c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d k
  disjoint d l
  disjoint F d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e k
  disjoint e l
  disjoint F e
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f l
  disjoint F f
  disjoint g h
  disjoint g k
  disjoint g l
  disjoint F g
  disjoint h k
  disjoint h l
  disjoint F h
  disjoint k l
  disjoint F k
  disjoint F l
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a k
  disjoint a l
  disjoint a x
  disjoint G a
  disjoint b x
  disjoint c x
  disjoint G c
  disjoint d x
  disjoint G d
  disjoint f x
  disjoint G f
  disjoint g x
  disjoint G g
  disjoint h x
  disjoint G h
  disjoint k x
  disjoint G k
  disjoint l x
  disjoint G l
  disjoint G x
  disjoint V f
  assert |- ( ( G e. V /\ ( F : _om --> ~P G /\ A. b e. _om ( F ` suc b ) C_ ( F ` b ) /\ -. |^| ran F e. ran F ) ) -> _om ~<_* G )

  proof
    com
    cG
    cpw
    cF
    wf
    #
    vb
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    wss
    #
    vb
    com
    wral
    #
    cF
    crn
    #
    cint
    @7
    wcel
    wn
    #
    w3a
    #
    cG
    cV
    wcel
    com
    cG
    cwdom
    wbr
    @9
    vc
    vd
    vh
    vg
    vf
    vk
    ve
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    wpss
    #
    ve
    com
    crab
    #
    cF
    cG
    vf
    com
    vg
    cv
    @15
    cin
    vf
    cv
    cen
    wbr
    vg
    @15
    crio
    cmpt
    #
    vh
    @15
    vh
    cv
    #
    cF
    cfv
    @17
    csuc
    cF
    cfv
    cdif
    cmpt
    @16
    ccom
    #
    vk
    cG
    vl
    cv
    #
    com
    wcel
    vk
    cv
    @19
    @18
    cfv
    wcel
    wa
    vl
    cio
    cmpt
    #
    cV
    vl
    @0
    @6
    @8
    simp1
    @6
    @0
    vc
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @21
    cF
    cfv
    #
    wss
    #
    vc
    com
    wral
    #
    @8
    @6
    @26
    @5
    @25
    vb
    vc
    com
    vb
    vc
    weq
    #
    @3
    @23
    @4
    @24
    @27
    @2
    @22
    cF
    @1
    @21
    suceq
    fveq2d
    @1
    @21
    cF
    fveq2
    sseq12d
    cbvralv
    biimpi
    3ad2ant2
    @0
    @6
    @8
    simp3
    @14
    vd
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @28
    cF
    cfv
    #
    wpss
    ve
    vd
    com
    ve
    vd
    weq
    #
    @12
    @30
    @13
    @31
    @32
    @11
    @29
    cF
    @10
    @28
    suceq
    fveq2d
    @10
    @28
    cF
    fveq2
    psseq12d
    cbvrabv
    @16
    eqid
    @18
    eqid
    @20
    eqid
    isf32lem10
    impcom
end
