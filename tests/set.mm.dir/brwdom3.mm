include "wcel.mm"
include "cvv.mm"
include "cwdom.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wex.mm"
include "wb.mm"
include "elex.mm"
include "wa.mm"
include "wfo.mm"
include "cpw.mm"
include "brwdom2.mm"
include "adantl.mm"
include "wf.mm"
include "dffo3.mm"
include "simprbi.mm"
include "wi.mm"
include "wss.mm"
include "elpwi.mm"
include "ssrexv.mm"
include "syl.mm"
include "ralimdv.mm"
include "syl5.mm"
include "eximdv.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "simpll.mm"
include "simplr.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "r19.21bi.mm"
include "wdom2d.mm"
include "ex.mm"
include "exlimdv.mm"
include "impbid.mm"
include "syl2an.mm"

theorem brwdom3
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z

  disjoint X f
  disjoint X x
  disjoint X y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint X w
  disjoint X z
  disjoint f w
  disjoint f z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint Y w
  disjoint Y z
  assert |- ( ( X e. V /\ Y e. W ) -> ( X ~<_* Y <-> E. f A. x e. X E. y e. Y x = ( f ` y ) ) )

  proof
    cX
    cV
    wcel
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    cX
    cY
    cwdom
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    wceq
    #
    vy
    cY
    wrex
    #
    vx
    cX
    wral
    #
    vf
    wex
    #
    wb
    cY
    cW
    wcel
    cX
    cV
    elex
    cY
    cW
    elex
    @0
    @1
    wa
    #
    @2
    @10
    @11
    @2
    vz
    cv
    #
    cX
    @5
    wfo
    #
    vf
    wex
    #
    vz
    cY
    cpw
    #
    wrex
    #
    @10
    @1
    @2
    @16
    wb
    @0
    vz
    vf
    cvv
    cX
    cY
    brwdom2
    adantl
    @11
    @14
    @10
    vz
    @15
    @11
    @12
    @15
    wcel
    #
    wa
    #
    @13
    @9
    vf
    @13
    @7
    vy
    @12
    wrex
    #
    vx
    cX
    wral
    #
    @18
    @9
    @13
    @12
    cX
    @5
    wf
    @20
    vy
    vx
    @12
    cX
    @5
    dffo3
    simprbi
    @18
    @19
    @8
    vx
    cX
    @17
    @19
    @8
    wi
    #
    @11
    @17
    @12
    cY
    wss
    @21
    @12
    cY
    elpwi
    @7
    vy
    @12
    cY
    ssrexv
    syl
    adantl
    ralimdv
    syl5
    eximdv
    rexlimdva
    sylbid
    @11
    @9
    @2
    vf
    @11
    @9
    @2
    @11
    @9
    wa
    #
    vz
    vw
    cX
    cY
    cvv
    cvv
    vw
    cv
    #
    @5
    cfv
    #
    @0
    @1
    @9
    simpll
    @0
    @1
    @9
    simplr
    @22
    @12
    @24
    wceq
    #
    vw
    cY
    wrex
    #
    vz
    cX
    @9
    @26
    vz
    cX
    wral
    #
    @11
    @9
    @27
    @8
    @26
    vx
    vz
    cX
    @3
    @12
    wceq
    #
    @8
    @12
    @6
    wceq
    #
    vy
    cY
    wrex
    @26
    @28
    @7
    @29
    vy
    cY
    @3
    @12
    @6
    eqeq1
    rexbidv
    @29
    @25
    vy
    vw
    cY
    @4
    @23
    wceq
    @6
    @24
    @12
    @4
    @23
    @5
    fveq2
    eqeq2d
    cbvrexv
    syl6bb
    cbvralv
    biimpi
    adantl
    r19.21bi
    wdom2d
    ex
    exlimdv
    impbid
    syl2an
end
