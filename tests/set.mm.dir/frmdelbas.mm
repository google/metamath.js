include "wcel.mm"
include "cword.mm"
include "id.mm"
include "cvv.mm"
include "wceq.mm"
include "cfrmd.mm"
include "elbasfv.mm"
include "frmdbas.mm"
include "syl.mm"
include "eleqtrd.mm"

theorem frmdelbas
  let cB: class B
  let cI: class I
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume frmdbas.m: |- M = ( freeMnd ` I )
  assume frmdbas.b: |- B = ( Base ` M )


  assert |- ( X e. B -> X e. Word I )

  proof
    cX
    cB
    wcel
    #
    cX
    cB
    cI
    cword
    #
    @0
    id
    @0
    cI
    cvv
    wcel
    cB
    @1
    wceq
    cB
    cM
    cfrmd
    cX
    cI
    frmdbas.m
    frmdbas.b
    elbasfv
    cB
    cI
    cM
    cvv
    frmdbas.m
    frmdbas.b
    frmdbas
    syl
    eleqtrd
end
