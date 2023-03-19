include "coml.mm"
include "wcel.mm"
include "col.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "rgen2a.mm"
include "isoml.mm"
include "mpbir2an.mm"

theorem isomliN
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  assume isomli.0: |- K e. OL
  assume isomli.b: |- B = ( Base ` K )
  assume isomli.l: |- .<_ = ( le ` K )
  assume isomli.j: |- .\/ = ( join ` K )
  assume isomli.m: |- ./\ = ( meet ` K )
  assume isomli.o: |- ._|_ = ( oc ` K )
  assume isomli.7: |- ( ( x e. B /\ y e. B ) -> ( x .<_ y -> y = ( x .\/ ( y ./\ ( ._|_ ` x ) ) ) ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  assert |- K e. OML

  proof
    cK
    coml
    wcel
    cK
    col
    wcel
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    @1
    @0
    @1
    @0
    c.pe
    cfv
    c.an
    co
    c.or
    co
    wceq
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    isomli.0
    @2
    vx
    vy
    cB
    isomli.7
    rgen2a
    vx
    vy
    cB
    c.or
    cK
    c.le
    c.an
    c.pe
    isomli.b
    isomli.l
    isomli.j
    isomli.m
    isomli.o
    isoml
    mpbir2an
end
