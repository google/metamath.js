include "cdr.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "wa.mm"
include "crg.mm"
include "wceq.mm"
include "isdrng.mm"
include "simprbi.mm"
include "eleq2d.mm"
include "eldifsn.mm"
include "syl6bb.mm"

theorem drngunit
  let cB: class B
  let cR: class R
  let cU: class U
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  assume isdrng.b: |- B = ( Base ` R )
  assume isdrng.u: |- U = ( Unit ` R )
  assume isdrng.z: |- .0. = ( 0g ` R )


  assert |- ( R e. DivRing -> ( X e. U <-> ( X e. B /\ X =/= .0. ) ) )

  proof
    cR
    cdr
    wcel
    #
    cX
    cU
    wcel
    cX
    cB
    c.0
    csn
    cdif
    #
    wcel
    cX
    cB
    wcel
    cX
    c.0
    wne
    wa
    @0
    cU
    @1
    cX
    @0
    cR
    crg
    wcel
    cU
    @1
    wceq
    cB
    cR
    cU
    c.0
    isdrng.b
    isdrng.u
    isdrng.z
    isdrng
    simprbi
    eleq2d
    cX
    cB
    c.0
    eldifsn
    syl6bb
end
