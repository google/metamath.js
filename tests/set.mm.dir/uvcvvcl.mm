include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "cpr.mm"
include "uvcvval.mm"
include "cvv.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifpr.mm"
include "mp2an.mm"
include "prcom.mm"
include "eleqtri.mm"
include "syl6eqel.mm"

theorem uvcvvcl
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vr: setvar r
  assume uvcfval.u: |- U = ( R unitVec I )
  assume uvcfval.o: |- .1. = ( 1r ` R )
  assume uvcfval.z: |- .0. = ( 0g ` R )


  assert |- ( ( ( R e. V /\ I e. W /\ J e. I ) /\ K e. I ) -> ( ( U ` J ) ` K ) e. { .0. , .1. } )

  proof
    cR
    cV
    wcel
    cI
    cW
    wcel
    cJ
    cI
    wcel
    w3a
    cK
    cI
    wcel
    wa
    cK
    cJ
    cU
    cfv
    cfv
    cK
    cJ
    wceq
    #
    c.1
    c.0
    cif
    #
    c.0
    c.1
    cpr
    #
    cR
    cU
    c.1
    cI
    cJ
    cK
    cV
    cW
    c.0
    uvcfval.u
    uvcfval.o
    uvcfval.z
    uvcvval
    @1
    c.1
    c.0
    cpr
    #
    @2
    c.1
    cvv
    wcel
    c.0
    cvv
    wcel
    @1
    @3
    wcel
    c.1
    cR
    cur
    cfv
    cvv
    uvcfval.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    uvcfval.z
    cR
    c0g
    fvex
    eqeltri
    @0
    c.1
    c.0
    cvv
    cvv
    ifpr
    mp2an
    c.1
    c.0
    prcom
    eleqtri
    syl6eqel
end
