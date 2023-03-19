include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "coc.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "col.mm"
include "coml.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "df-oml.mm"
include "elrab2.mm"

theorem isoml
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let vk: setvar k
  assume isoml.b: |- B = ( Base ` K )
  assume isoml.l: |- .<_ = ( le ` K )
  assume isoml.j: |- .\/ = ( join ` K )
  assume isoml.m: |- ./\ = ( meet ` K )
  assume isoml.o: |- ._|_ = ( oc ` K )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint .\/ k
  disjoint K k
  disjoint ./\ k
  disjoint ._|_ k
  disjoint .<_ k
  assert |- ( K e. OML <-> ( K e. OL /\ A. x e. B A. y e. B ( x .<_ y -> y = ( x .\/ ( y ./\ ( ._|_ ` x ) ) ) ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vk
    cv
    #
    cple
    cfv
    #
    wbr
    #
    @1
    @0
    @1
    @0
    @2
    coc
    cfv
    #
    cfv
    #
    @2
    cmee
    cfv
    #
    co
    #
    @2
    cjn
    cfv
    #
    co
    #
    wceq
    #
    wi
    #
    vy
    @2
    cbs
    cfv
    #
    wral
    #
    vx
    @13
    wral
    @0
    @1
    c.le
    wbr
    #
    @1
    @0
    @1
    @0
    c.pe
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    vk
    cK
    col
    coml
    @2
    cK
    wceq
    #
    @14
    @21
    vx
    @13
    cB
    @22
    @13
    cK
    cbs
    cfv
    cB
    @2
    cK
    cbs
    fveq2
    isoml.b
    syl6eqr
    #
    @22
    @12
    @20
    vy
    @13
    cB
    @23
    @22
    @4
    @15
    @11
    @19
    @22
    @3
    c.le
    @0
    @1
    @22
    @3
    cK
    cple
    cfv
    c.le
    @2
    cK
    cple
    fveq2
    isoml.l
    syl6eqr
    breqd
    @22
    @10
    @18
    @1
    @22
    @0
    @0
    @8
    @17
    @9
    c.or
    @22
    @9
    cK
    cjn
    cfv
    c.or
    @2
    cK
    cjn
    fveq2
    isoml.j
    syl6eqr
    @22
    @0
    eqidd
    @22
    @1
    @1
    @6
    @16
    @7
    c.an
    @22
    @7
    cK
    cmee
    cfv
    c.an
    @2
    cK
    cmee
    fveq2
    isoml.m
    syl6eqr
    @22
    @1
    eqidd
    @22
    @0
    @5
    c.pe
    @22
    @5
    cK
    coc
    cfv
    c.pe
    @2
    cK
    coc
    fveq2
    isoml.o
    syl6eqr
    fveq1d
    oveq123d
    oveq123d
    eqeq2d
    imbi12d
    raleqbidv
    raleqbidv
    vx
    vy
    vk
    df-oml
    elrab2
end
