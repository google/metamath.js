include "cui.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "cdr.mm"
include "wa.mm"
include "eqid.mm"
include "isdrng.mm"
include "mpbi.mm"
include "simpri.mm"
include "eqcomi.mm"

theorem drngui
  let cB: class B
  let cR: class R
  let c.0: class .0.
  assume drngui.b: |- B = ( Base ` R )
  assume drngui.z: |- .0. = ( 0g ` R )
  assume drngui.r: |- R e. DivRing


  assert |- ( B \ { .0. } ) = ( Unit ` R )

  proof
    cR
    cui
    cfv
    #
    cB
    c.0
    csn
    cdif
    #
    cR
    crg
    wcel
    #
    @0
    @1
    wceq
    #
    cR
    cdr
    wcel
    @2
    @3
    wa
    drngui.r
    cB
    cR
    @0
    c.0
    drngui.b
    @0
    eqid
    drngui.z
    isdrng
    mpbi
    simpri
    eqcomi
end
