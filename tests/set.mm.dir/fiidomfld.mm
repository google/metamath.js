include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "cdomn.mm"
include "wa.mm"
include "cdr.mm"
include "cidom.mm"
include "cfield.mm"
include "fidomndrng.mm"
include "anbi2d.mm"
include "isidom.mm"
include "isfld.mm"
include "ancom.mm"
include "bitri.mm"
include "3bitr4g.mm"

theorem fiidomfld
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let wph: wff ph
  let c.x: class .x.
  let c.1: class .1.
  let c.0: class .0.
  assume fidomndrng.b: |- B = ( Base ` R )


  assert |- ( B e. Fin -> ( R e. IDomn <-> R e. Field ) )

  proof
    cB
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cR
    cdomn
    wcel
    #
    wa
    @1
    cR
    cdr
    wcel
    #
    wa
    #
    cR
    cidom
    wcel
    cR
    cfield
    wcel
    #
    @0
    @2
    @3
    @1
    cB
    cR
    fidomndrng.b
    fidomndrng
    anbi2d
    cR
    isidom
    @5
    @3
    @1
    wa
    @4
    cR
    isfld
    @3
    @1
    ancom
    bitri
    3bitr4g
end
