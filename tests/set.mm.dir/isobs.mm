include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "cphl.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "wral.mm"
include "csn.mm"
include "wa.mm"
include "w3a.mm"
include "cdm.mm"
include "cip.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "cocv.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "df-obs.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "ifeq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "fveq1d.mm"
include "sneqd.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "biadan2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isobs
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.1: class .1.
  let cF: class F
  let c.xi: class .,
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vb: setvar b
  let vh: setvar h
  let cP: class P
  let cQ: class Q
  assume isobs.v: |- V = ( Base ` W )
  assume isobs.h: |- ., = ( .i ` W )
  assume isobs.f: |- F = ( Scalar ` W )
  assume isobs.u: |- .1. = ( 1r ` F )
  assume isobs.z: |- .0. = ( 0g ` F )
  assume isobs.o: |- ._|_ = ( ocv ` W )
  assume isobs.y: |- Y = ( 0g ` W )

  disjoint x y
  disjoint ., x
  disjoint ., y
  disjoint .0. x
  disjoint .0. y
  disjoint .1. x
  disjoint .1. y
  disjoint B x
  disjoint B y
  disjoint W x
  disjoint W y
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint ., b
  disjoint h x
  disjoint h y
  disjoint ., h
  disjoint ._|_ b
  disjoint ._|_ h
  disjoint .0. b
  disjoint .0. h
  disjoint P x
  disjoint P y
  disjoint Q y
  disjoint .1. b
  disjoint .1. h
  disjoint B b
  disjoint V b
  disjoint V h
  disjoint W b
  disjoint W h
  disjoint Y b
  disjoint Y h
  assert |- ( B e. ( OBasis ` W ) <-> ( W e. PreHil /\ B C_ V /\ ( A. x e. B A. y e. B ( x ., y ) = if ( x = y , .1. , .0. ) /\ ( ._|_ ` B ) = { Y } ) ) )

  proof
    cB
    cW
    cobs
    cfv
    #
    wcel
    #
    cW
    cphl
    wcel
    #
    cB
    cV
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    #
    @4
    @5
    wceq
    #
    c.1
    c.0
    cif
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    cB
    c.pe
    cfv
    #
    cY
    csn
    #
    wceq
    #
    wa
    #
    wa
    #
    wa
    @2
    @3
    @15
    w3a
    @1
    @2
    @16
    @1
    cobs
    cdm
    cphl
    cW
    vh
    cphl
    @4
    @5
    vh
    cv
    #
    cip
    cfv
    #
    co
    #
    @7
    @17
    csca
    cfv
    #
    cur
    cfv
    #
    @20
    c0g
    cfv
    #
    cif
    #
    wceq
    #
    vy
    vb
    cv
    #
    wral
    vx
    @25
    wral
    #
    @25
    @17
    cocv
    cfv
    #
    cfv
    #
    @17
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wa
    #
    vb
    @17
    cbs
    cfv
    #
    cpw
    #
    crab
    #
    cobs
    vx
    vy
    vh
    vb
    df-obs
    #
    dmmptss
    cB
    cW
    cobs
    elfvdm
    sseldi
    @2
    @1
    cB
    @9
    vy
    @25
    wral
    #
    vx
    @25
    wral
    #
    @25
    c.pe
    cfv
    #
    @13
    wceq
    #
    wa
    #
    vb
    cV
    cpw
    #
    crab
    #
    wcel
    #
    @16
    @2
    @0
    @43
    cB
    vh
    cW
    @35
    @43
    cphl
    cobs
    @17
    cW
    wceq
    #
    @32
    @41
    vb
    @34
    @42
    @45
    @33
    cV
    @45
    @33
    cW
    cbs
    cfv
    #
    cV
    @17
    cW
    cbs
    fveq2
    isobs.v
    syl6eqr
    pweqd
    @45
    @26
    @38
    @31
    @40
    @45
    @24
    @9
    vx
    vy
    @25
    @25
    @45
    @19
    @6
    @23
    @8
    @45
    @18
    c.xi
    @4
    @5
    @45
    @18
    cW
    cip
    cfv
    c.xi
    @17
    cW
    cip
    fveq2
    isobs.h
    syl6eqr
    oveqd
    @45
    @7
    @21
    c.1
    @22
    c.0
    @45
    @21
    cF
    cur
    cfv
    c.1
    @45
    @20
    cF
    cur
    @45
    @20
    cW
    csca
    cfv
    cF
    @17
    cW
    csca
    fveq2
    isobs.f
    syl6eqr
    #
    fveq2d
    isobs.u
    syl6eqr
    @45
    @22
    cF
    c0g
    cfv
    c.0
    @45
    @20
    cF
    c0g
    @47
    fveq2d
    isobs.z
    syl6eqr
    ifeq12d
    eqeq12d
    2ralbidv
    @45
    @28
    @39
    @30
    @13
    @45
    @25
    @27
    c.pe
    @45
    @27
    cW
    cocv
    cfv
    c.pe
    @17
    cW
    cocv
    fveq2
    isobs.o
    syl6eqr
    fveq1d
    @45
    @29
    cY
    @45
    @29
    cW
    c0g
    cfv
    cY
    @17
    cW
    c0g
    fveq2
    isobs.y
    syl6eqr
    sneqd
    eqeq12d
    anbi12d
    rabeqbidv
    @36
    @41
    vb
    @42
    cV
    cV
    @46
    cvv
    isobs.v
    cW
    cbs
    fvex
    eqeltri
    #
    pwex
    rabex
    fvmpt
    eleq2d
    @44
    cB
    @42
    wcel
    #
    @15
    wa
    @16
    @41
    @15
    vb
    cB
    @42
    @25
    cB
    wceq
    #
    @38
    @11
    @40
    @14
    @37
    @10
    vx
    @25
    cB
    @9
    vy
    @25
    cB
    raleq
    raleqbi1dv
    @50
    @39
    @12
    @13
    @25
    cB
    c.pe
    fveq2
    eqeq1d
    anbi12d
    elrab
    @49
    @3
    @15
    cB
    cV
    @48
    elpw2
    anbi1i
    bitri
    syl6bb
    biadan2
    @2
    @3
    @15
    3anass
    bitr4i
end
