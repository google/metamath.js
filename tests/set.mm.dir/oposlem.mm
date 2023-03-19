include "cops.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cpo.mm"
include "club.mm"
include "cdm.mm"
include "cglb.mm"
include "eqid.mm"
include "isopos.mm"
include "simprbi.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "breq1.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "3anbi123d.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "breq2.mm"
include "breq1d.mm"
include "3anbi3d.mm"
include "3anbi1d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "3impb.mm"

theorem oposlem
  let cB: class B
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume oposlem.b: |- B = ( Base ` K )
  assume oposlem.l: |- .<_ = ( le ` K )
  assume oposlem.o: |- ._|_ = ( oc ` K )
  assume oposlem.j: |- .\/ = ( join ` K )
  assume oposlem.m: |- ./\ = ( meet ` K )
  assume oposlem.f: |- .0. = ( 0. ` K )
  assume oposlem.u: |- .1. = ( 1. ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( ( ( ._|_ ` X ) e. B /\ ( ._|_ ` ( ._|_ ` X ) ) = X /\ ( X .<_ Y -> ( ._|_ ` Y ) .<_ ( ._|_ ` X ) ) ) /\ ( X .\/ ( ._|_ ` X ) ) = .1. /\ ( X ./\ ( ._|_ ` X ) ) = .0. ) )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    c.pe
    cfv
    #
    cB
    wcel
    #
    @3
    c.pe
    cfv
    #
    cX
    wceq
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    c.pe
    cfv
    #
    @3
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    cX
    @3
    c.or
    co
    #
    c.1
    wceq
    #
    cX
    @3
    c.an
    co
    #
    c.0
    wceq
    #
    w3a
    #
    @0
    vx
    cv
    #
    c.pe
    cfv
    #
    cB
    wcel
    #
    @18
    c.pe
    cfv
    #
    @17
    wceq
    #
    @17
    vy
    cv
    #
    c.le
    wbr
    #
    @22
    c.pe
    cfv
    #
    @18
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    @17
    @18
    c.or
    co
    #
    c.1
    wceq
    #
    @17
    @18
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
    @1
    @2
    wa
    @16
    @0
    cK
    cpo
    wcel
    cB
    cK
    club
    cfv
    #
    cdm
    wcel
    cB
    cK
    cglb
    cfv
    #
    cdm
    wcel
    w3a
    @33
    vx
    vy
    cB
    @34
    c.1
    @35
    c.or
    cK
    c.le
    c.an
    c.pe
    c.0
    oposlem.b
    @34
    eqid
    @35
    eqid
    oposlem.l
    oposlem.o
    oposlem.j
    oposlem.m
    oposlem.f
    oposlem.u
    isopos
    simprbi
    @32
    @16
    @4
    @6
    cX
    @22
    c.le
    wbr
    #
    @24
    @3
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    @13
    @15
    w3a
    vx
    vy
    cX
    cY
    cB
    cB
    @17
    cX
    wceq
    #
    @27
    @39
    @29
    @13
    @31
    @15
    @40
    @19
    @4
    @21
    @6
    @26
    @38
    @40
    @18
    @3
    cB
    @17
    cX
    c.pe
    fveq2
    #
    eleq1d
    @40
    @20
    @5
    @17
    cX
    @40
    @18
    @3
    c.pe
    @41
    fveq2d
    @40
    id
    #
    eqeq12d
    @40
    @23
    @36
    @25
    @37
    @17
    cX
    @22
    c.le
    breq1
    @40
    @18
    @3
    @24
    c.le
    @41
    breq2d
    imbi12d
    3anbi123d
    @40
    @28
    @12
    c.1
    @40
    @17
    cX
    @18
    @3
    c.or
    @42
    @41
    oveq12d
    eqeq1d
    @40
    @30
    @14
    c.0
    @40
    @17
    cX
    @18
    @3
    c.an
    @42
    @41
    oveq12d
    eqeq1d
    3anbi123d
    @22
    cY
    wceq
    #
    @39
    @11
    @13
    @15
    @43
    @38
    @10
    @4
    @6
    @43
    @36
    @7
    @37
    @9
    @22
    cY
    cX
    c.le
    breq2
    @43
    @24
    @8
    @3
    c.le
    @22
    cY
    c.pe
    fveq2
    breq1d
    imbi12d
    3anbi3d
    3anbi1d
    rspc2v
    mpan9
    3impb
end
