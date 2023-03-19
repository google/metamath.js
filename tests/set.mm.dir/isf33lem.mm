include "cfin3.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "com.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wcel.mm"
include "wi.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cab.mm"
include "cwdom.mm"
include "wbr.mm"
include "wn.mm"
include "isfin32i.mm"
include "weq.mm"
include "fveq1.mm"
include "sseq12d.mm"
include "ralbidv.mm"
include "rneq.mm"
include "inteqd.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "pweq.mm"
include "oveq1d.mm"
include "raleqdv.mm"
include "syl5bb.mm"
include "cbvabv.mm"
include "isf32lem12.mm"
include "mpd.mm"
include "abbii.mm"
include "fin23lem41.mm"
include "impbii.mm"
include "eqriv.mm"

theorem isf33lem
  let vx: setvar x
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cV: class V

  disjoint a g
  disjoint a x
  disjoint g x
  disjoint a b
  disjoint a f
  disjoint a y
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V x
  assert |- Fin3 = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }

  proof
    vf
    cfin3
    vx
    cv
    #
    csuc
    #
    va
    cv
    #
    cfv
    #
    @0
    @2
    cfv
    #
    wss
    #
    vx
    com
    wral
    #
    @2
    crn
    #
    cint
    #
    @7
    wcel
    #
    wi
    #
    va
    vg
    cv
    #
    cpw
    #
    com
    cmap
    co
    #
    wral
    #
    vg
    cab
    #
    vf
    cv
    #
    cfin3
    wcel
    #
    @16
    @15
    wcel
    #
    @17
    com
    @16
    cwdom
    wbr
    wn
    @18
    @16
    isfin32i
    vx
    vy
    @15
    @16
    cfin3
    vb
    @14
    @1
    vb
    cv
    #
    cfv
    #
    @0
    @19
    cfv
    #
    wss
    #
    vx
    com
    wral
    #
    @19
    crn
    #
    cint
    #
    @24
    wcel
    #
    wi
    #
    vb
    vy
    cv
    #
    cpw
    #
    com
    cmap
    co
    #
    wral
    #
    vg
    vy
    @14
    @27
    vb
    @13
    wral
    #
    vg
    vy
    weq
    #
    @31
    @10
    @27
    va
    vb
    @13
    va
    vb
    weq
    #
    @6
    @23
    @9
    @26
    @34
    @5
    @22
    vx
    com
    @34
    @3
    @20
    @4
    @21
    @1
    @2
    @19
    fveq1
    @0
    @2
    @19
    fveq1
    sseq12d
    ralbidv
    @34
    @8
    @25
    @7
    @24
    @34
    @7
    @24
    @2
    @19
    rneq
    #
    inteqd
    @35
    eleq12d
    imbi12d
    cbvralv
    #
    @33
    @27
    vb
    @13
    @30
    @33
    @12
    @29
    com
    cmap
    @11
    @28
    pweq
    oveq1d
    raleqdv
    syl5bb
    cbvabv
    isf32lem12
    mpd
    vx
    @16
    vg
    @15
    vb
    @14
    @32
    vg
    @36
    abbii
    fin23lem41
    impbii
    eqriv
end
