include "cpo.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "w3a.mm"
include "wral.mm"
include "cvv.mm"
include "ispos.mm"
include "simprbi.mm"
include "breq1.mm"
include "breq2.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "anbi1d.mm"
include "3anbi123d.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "3anbi23d.mm"
include "anbi2d.mm"
include "3anbi3d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem posi
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume posi.b: |- B = ( Base ` K )
  assume posi.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ X /\ ( ( X .<_ Y /\ Y .<_ X ) -> X = Y ) /\ ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) )

  proof
    cK
    cpo
    wcel
    #
    vx
    cv
    #
    @1
    c.le
    wbr
    #
    @1
    vy
    cv
    #
    c.le
    wbr
    #
    @3
    @1
    c.le
    wbr
    #
    wa
    #
    @1
    @3
    wceq
    #
    wi
    #
    @4
    @3
    vz
    cv
    #
    c.le
    wbr
    #
    wa
    #
    @1
    @9
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cX
    c.le
    wbr
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    wceq
    #
    wi
    #
    @17
    cY
    cZ
    c.le
    wbr
    #
    wa
    #
    cX
    cZ
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    @0
    cK
    cvv
    wcel
    @15
    vx
    vy
    vz
    cB
    cK
    c.le
    posi.b
    posi.l
    ispos
    simprbi
    @14
    @26
    @16
    cX
    @3
    c.le
    wbr
    #
    @3
    cX
    c.le
    wbr
    #
    wa
    #
    cX
    @3
    wceq
    #
    wi
    #
    @27
    @10
    wa
    #
    cX
    @9
    c.le
    wbr
    #
    wi
    #
    w3a
    @16
    @21
    @17
    cY
    @9
    c.le
    wbr
    #
    wa
    #
    @33
    wi
    #
    w3a
    vx
    vy
    vz
    cX
    cY
    cZ
    cB
    cB
    cB
    @1
    cX
    wceq
    #
    @2
    @16
    @8
    @31
    @13
    @34
    @38
    @2
    cX
    @1
    c.le
    wbr
    @16
    @1
    cX
    @1
    c.le
    breq1
    @1
    cX
    cX
    c.le
    breq2
    bitrd
    @38
    @6
    @29
    @7
    @30
    @38
    @4
    @27
    @5
    @28
    @1
    cX
    @3
    c.le
    breq1
    #
    @1
    cX
    @3
    c.le
    breq2
    anbi12d
    @1
    cX
    @3
    eqeq1
    imbi12d
    @38
    @11
    @32
    @12
    @33
    @38
    @4
    @27
    @10
    @39
    anbi1d
    @1
    cX
    @9
    c.le
    breq1
    imbi12d
    3anbi123d
    @3
    cY
    wceq
    #
    @31
    @21
    @34
    @37
    @16
    @40
    @29
    @19
    @30
    @20
    @40
    @27
    @17
    @28
    @18
    @3
    cY
    cX
    c.le
    breq2
    #
    @3
    cY
    cX
    c.le
    breq1
    anbi12d
    @3
    cY
    cX
    eqeq2
    imbi12d
    @40
    @32
    @36
    @33
    @40
    @27
    @17
    @10
    @35
    @41
    @3
    cY
    @9
    c.le
    breq1
    anbi12d
    imbi1d
    3anbi23d
    @9
    cZ
    wceq
    #
    @37
    @25
    @16
    @21
    @42
    @36
    @23
    @33
    @24
    @42
    @35
    @22
    @17
    @9
    cZ
    cY
    c.le
    breq2
    anbi2d
    @9
    cZ
    cX
    c.le
    breq2
    imbi12d
    3anbi3d
    rspc3v
    mpan9
end
