include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "rerpdivcl.mm"
include "fllelt.mm"
include "simpl.mm"
include "3syl.mm"

theorem fldivle
  let cK: class K
  let cL: class L


  assert |- ( ( K e. RR /\ L e. RR+ ) -> ( |_ ` ( K / L ) ) <_ ( K / L ) )

  proof
    cK
    cr
    wcel
    cL
    crp
    wcel
    wa
    cK
    cL
    cdiv
    co
    #
    cr
    wcel
    @0
    cfl
    cfv
    #
    @0
    cle
    wbr
    #
    @0
    @1
    c1
    caddc
    co
    clt
    wbr
    #
    wa
    @2
    cK
    cL
    rerpdivcl
    @0
    fllelt
    @2
    @3
    simpl
    3syl
end
