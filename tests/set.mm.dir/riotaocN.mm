include "cops.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "crio.mm"
include "nfcv.mm"
include "nfriota1.mm"
include "nffv.mm"
include "opoccl.mm"
include "fveq2.mm"
include "opcon2b.mm"
include "reuhypd.mm"
include "riotaxfrd.mm"

theorem riotaocN
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let c.pe: class ._|_
  assume riotaoc.b: |- B = ( Base ` K )
  assume riotaoc.o: |- ._|_ = ( oc ` K )
  assume riotaoc.a: |- ( x = ( ._|_ ` y ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ._|_ x
  disjoint ._|_ y
  disjoint ph y
  disjoint ps x
  assert |- ( ( K e. OP /\ E! x e. B ph ) -> ( iota_ x e. B ph ) = ( ._|_ ` ( iota_ y e. B ps ) ) )

  proof
    cK
    cops
    wcel
    #
    wph
    wps
    vx
    vy
    cB
    vy
    cv
    #
    c.pe
    cfv
    #
    wps
    vy
    cB
    crio
    #
    c.pe
    cfv
    vy
    @3
    c.pe
    vy
    c.pe
    nfcv
    wps
    vy
    cB
    nfriota1
    nffv
    cB
    cK
    c.pe
    @1
    riotaoc.b
    riotaoc.o
    opoccl
    cB
    cK
    c.pe
    @3
    riotaoc.b
    riotaoc.o
    opoccl
    riotaoc.a
    @1
    @3
    c.pe
    fveq2
    @0
    vx
    vy
    @2
    vx
    cv
    #
    c.pe
    cfv
    cB
    cB
    cK
    c.pe
    @4
    riotaoc.b
    riotaoc.o
    opoccl
    cB
    cK
    c.pe
    @4
    @1
    riotaoc.b
    riotaoc.o
    opcon2b
    reuhypd
    riotaxfrd
end
