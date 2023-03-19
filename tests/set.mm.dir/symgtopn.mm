include "wcel.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cts.mm"
include "ctopn.mm"
include "symgtset.mm"
include "oveq1d.mm"
include "eqid.mm"
include "topnval.mm"
include "syl6eq.mm"

theorem symgtopn
  let cB: class B
  let cG: class G
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume symgga.g: |- G = ( SymGrp ` X )
  assume symgga.b: |- B = ( Base ` G )


  assert |- ( X e. V -> ( ( Xt_ ` ( X X. { ~P X } ) ) |`t B ) = ( TopOpen ` G ) )

  proof
    cX
    cV
    wcel
    #
    cX
    cX
    cpw
    csn
    cxp
    cpt
    cfv
    #
    cB
    crest
    co
    cG
    cts
    cfv
    #
    cB
    crest
    co
    cG
    ctopn
    cfv
    @0
    @1
    @2
    cB
    crest
    cX
    cG
    cV
    symgga.g
    symgtset
    oveq1d
    cB
    @2
    cG
    symgga.b
    @2
    eqid
    topnval
    syl6eq
end
