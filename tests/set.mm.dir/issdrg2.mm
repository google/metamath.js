include "csdrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cdr.mm"
include "csubrg.mm"
include "cress.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "issdrg.mm"
include "wa.mm"
include "eqid.mm"
include "issubdrg.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem issdrg2
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cI: class I
  let c.0: class .0.
  assume issdrg2.i: |- I = ( invr ` R )
  assume issdrg2.z: |- .0. = ( 0g ` R )

  disjoint R x
  disjoint S x
  disjoint .0. x
  assert |- ( S e. ( SubDRing ` R ) <-> ( R e. DivRing /\ S e. ( SubRing ` R ) /\ A. x e. ( S \ { .0. } ) ( I ` x ) e. S ) )

  proof
    cS
    cR
    csdrg
    cfv
    wcel
    cR
    cdr
    wcel
    #
    cS
    cR
    csubrg
    cfv
    wcel
    #
    cR
    cS
    cress
    co
    #
    cdr
    wcel
    #
    w3a
    #
    @0
    @1
    vx
    cv
    cI
    cfv
    cS
    wcel
    vx
    cS
    c.0
    csn
    cdif
    wral
    #
    w3a
    #
    cR
    cS
    issdrg
    @0
    @1
    wa
    #
    @3
    wa
    @7
    @5
    wa
    @4
    @6
    @7
    @3
    @5
    vx
    cS
    cR
    @2
    cI
    c.0
    @2
    eqid
    issdrg2.z
    issdrg2.i
    issubdrg
    pm5.32i
    @0
    @1
    @3
    df-3an
    @0
    @1
    @5
    df-3an
    3bitr4i
    bitri
end
