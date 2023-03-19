include "cops.mm"
include "wcel.mm"
include "cpo.mm"
include "cdm.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "co.mm"
include "wral.mm"
include "wex.mm"
include "cbs.mm"
include "club.mm"
include "cglb.mm"
include "coc.mm"
include "cple.mm"
include "cjn.mm"
include "cp1.mm"
include "cmee.mm"
include "cp0.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "eleq2d.mm"
include "breqd.mm"
include "imbi12d.mm"
include "3anbi13d.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "raleqbidv.mm"
include "exbidv.mm"
include "df-oposet.mm"
include "elrab2.mm"
include "anass.mm"
include "3anass.mm"
include "bicomi.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "id.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "oveq2d.mm"
include "2ralbidv.mm"
include "ceqsexv.mm"
include "anbi12i.mm"
include "3bitr2i.mm"

theorem isopos
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let c.0: class .0.
  let vn: setvar n
  let vp: setvar p
  assume isopos.b: |- B = ( Base ` K )
  assume isopos.e: |- U = ( lub ` K )
  assume isopos.g: |- G = ( glb ` K )
  assume isopos.l: |- .<_ = ( le ` K )
  assume isopos.o: |- ._|_ = ( oc ` K )
  assume isopos.j: |- .\/ = ( join ` K )
  assume isopos.m: |- ./\ = ( meet ` K )
  assume isopos.f: |- .0. = ( 0. ` K )
  assume isopos.u: |- .1. = ( 1. ` K )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ._|_ x
  disjoint ._|_ y
  disjoint K x
  disjoint K y
  disjoint n p
  disjoint .\/ n
  disjoint .\/ p
  disjoint .<_ n
  disjoint .<_ p
  disjoint ./\ n
  disjoint ./\ p
  disjoint .0. n
  disjoint .0. p
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint p x
  disjoint p y
  disjoint B p
  disjoint ._|_ n
  disjoint ._|_ p
  disjoint .1. n
  disjoint .1. p
  disjoint K n
  disjoint K p
  disjoint U p
  disjoint G p
  assert |- ( K e. OP <-> ( ( K e. Poset /\ B e. dom U /\ B e. dom G ) /\ A. x e. B A. y e. B ( ( ( ._|_ ` x ) e. B /\ ( ._|_ ` ( ._|_ ` x ) ) = x /\ ( x .<_ y -> ( ._|_ ` y ) .<_ ( ._|_ ` x ) ) ) /\ ( x .\/ ( ._|_ ` x ) ) = .1. /\ ( x ./\ ( ._|_ ` x ) ) = .0. ) ) )

  proof
    cK
    cops
    wcel
    cK
    cpo
    wcel
    #
    cB
    cU
    cdm
    #
    wcel
    #
    cB
    cG
    cdm
    #
    wcel
    #
    wa
    #
    vn
    cv
    #
    c.pe
    wceq
    #
    vx
    cv
    #
    @6
    cfv
    #
    cB
    wcel
    #
    @9
    @6
    cfv
    #
    @8
    wceq
    #
    @8
    vy
    cv
    #
    c.le
    wbr
    #
    @13
    @6
    cfv
    #
    @9
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    @8
    @9
    c.or
    co
    #
    c.1
    wceq
    #
    @8
    @9
    c.an
    co
    #
    c.0
    wceq
    #
    w3a
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vn
    wex
    #
    wa
    #
    wa
    @0
    @5
    wa
    #
    @27
    wa
    @0
    @2
    @4
    w3a
    #
    @8
    c.pe
    cfv
    #
    cB
    wcel
    #
    @31
    c.pe
    cfv
    #
    @8
    wceq
    #
    @14
    @13
    c.pe
    cfv
    #
    @31
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    @8
    @31
    c.or
    co
    #
    c.1
    wceq
    #
    @8
    @31
    c.an
    co
    #
    c.0
    wceq
    #
    w3a
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    vp
    cv
    #
    cbs
    cfv
    #
    @45
    club
    cfv
    #
    cdm
    #
    wcel
    #
    @46
    @45
    cglb
    cfv
    #
    cdm
    #
    wcel
    #
    wa
    #
    @6
    @45
    coc
    cfv
    #
    wceq
    #
    @9
    @46
    wcel
    #
    @12
    @8
    @13
    @45
    cple
    cfv
    #
    wbr
    #
    @15
    @9
    @57
    wbr
    #
    wi
    #
    w3a
    #
    @8
    @9
    @45
    cjn
    cfv
    #
    co
    #
    @45
    cp1
    cfv
    #
    wceq
    #
    @8
    @9
    @45
    cmee
    cfv
    #
    co
    #
    @45
    cp0
    cfv
    #
    wceq
    #
    w3a
    #
    vy
    @46
    wral
    #
    vx
    @46
    wral
    #
    wa
    #
    vn
    wex
    #
    wa
    @28
    vp
    cK
    cpo
    cops
    @45
    cK
    wceq
    #
    @53
    @5
    @74
    @27
    @75
    @49
    @2
    @52
    @4
    @75
    @46
    cB
    @48
    @1
    @75
    @46
    cK
    cbs
    cfv
    cB
    @45
    cK
    cbs
    fveq2
    isopos.b
    syl6eqr
    #
    @75
    @47
    cU
    @75
    @47
    cK
    club
    cfv
    cU
    @45
    cK
    club
    fveq2
    isopos.e
    syl6eqr
    dmeqd
    eleq12d
    @75
    @46
    cB
    @51
    @3
    @76
    @75
    @50
    cG
    @75
    @50
    cK
    cglb
    cfv
    cG
    @45
    cK
    cglb
    fveq2
    isopos.g
    syl6eqr
    dmeqd
    eleq12d
    anbi12d
    @75
    @73
    @26
    vn
    @75
    @55
    @7
    @72
    @25
    @75
    @54
    c.pe
    @6
    @75
    @54
    cK
    coc
    cfv
    #
    c.pe
    @45
    cK
    coc
    fveq2
    isopos.o
    syl6eqr
    eqeq2d
    @75
    @71
    @24
    vx
    @46
    cB
    @76
    @75
    @70
    @23
    vy
    @46
    cB
    @76
    @75
    @61
    @18
    @65
    @20
    @69
    @22
    @75
    @56
    @10
    @60
    @17
    @12
    @75
    @46
    cB
    @9
    @76
    eleq2d
    @75
    @58
    @14
    @59
    @16
    @75
    @57
    c.le
    @8
    @13
    @75
    @57
    cK
    cple
    cfv
    c.le
    @45
    cK
    cple
    fveq2
    isopos.l
    syl6eqr
    #
    breqd
    @75
    @57
    c.le
    @15
    @9
    @78
    breqd
    imbi12d
    3anbi13d
    @75
    @63
    @19
    @64
    c.1
    @75
    @62
    c.or
    @8
    @9
    @75
    @62
    cK
    cjn
    cfv
    c.or
    @45
    cK
    cjn
    fveq2
    isopos.j
    syl6eqr
    oveqd
    @75
    @64
    cK
    cp1
    cfv
    c.1
    @45
    cK
    cp1
    fveq2
    isopos.u
    syl6eqr
    eqeq12d
    @75
    @67
    @21
    @68
    c.0
    @75
    @66
    c.an
    @8
    @9
    @75
    @66
    cK
    cmee
    cfv
    c.an
    @45
    cK
    cmee
    fveq2
    isopos.m
    syl6eqr
    oveqd
    @75
    @68
    cK
    cp0
    cfv
    c.0
    @45
    cK
    cp0
    fveq2
    isopos.f
    syl6eqr
    eqeq12d
    3anbi123d
    raleqbidv
    raleqbidv
    anbi12d
    exbidv
    anbi12d
    vn
    vp
    vx
    vy
    df-oposet
    elrab2
    @0
    @5
    @27
    anass
    @29
    @30
    @27
    @44
    @30
    @29
    @0
    @2
    @4
    3anass
    bicomi
    @25
    @44
    vn
    c.pe
    c.pe
    @77
    cvv
    isopos.o
    cK
    coc
    fvex
    eqeltri
    @7
    @23
    @43
    vx
    vy
    cB
    cB
    @7
    @18
    @38
    @20
    @40
    @22
    @42
    @7
    @10
    @32
    @12
    @34
    @17
    @37
    @7
    @9
    @31
    cB
    @8
    @6
    c.pe
    fveq1
    #
    eleq1d
    @7
    @11
    @33
    @8
    @7
    @9
    @31
    @6
    c.pe
    @7
    id
    @79
    fveq12d
    eqeq1d
    @7
    @16
    @36
    @14
    @7
    @15
    @35
    @9
    @31
    c.le
    @13
    @6
    c.pe
    fveq1
    @79
    breq12d
    imbi2d
    3anbi123d
    @7
    @19
    @39
    c.1
    @7
    @9
    @31
    @8
    c.or
    @79
    oveq2d
    eqeq1d
    @7
    @21
    @41
    c.0
    @7
    @9
    @31
    @8
    c.an
    @79
    oveq2d
    eqeq1d
    3anbi123d
    2ralbidv
    ceqsexv
    anbi12i
    3bitr2i
end
