include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "cfallfac.mm"
include "cbc.mm"
include "cn0.mm"
include "cn.mm"
include "elfz3nn0.mm"
include "faccl.mm"
include "syl.mm"
include "nncnd.mm"
include "fznn0sub.mm"
include "elfznn0.mm"
include "nnne0d.mm"
include "divdiv1d.mm"
include "fallfacval4.mm"
include "oveq1d.mm"
include "bcval2.mm"
include "3eqtr4rd.mm"

theorem bcfallfac
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> ( N _C K ) = ( ( N FallFac K ) / ( ! ` K ) ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cfa
    cfv
    #
    cN
    cK
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cK
    cfa
    cfv
    #
    cdiv
    co
    @1
    @3
    @5
    cmul
    co
    cdiv
    co
    cN
    cK
    cfallfac
    co
    #
    @5
    cdiv
    co
    cN
    cK
    cbc
    co
    @0
    @1
    @3
    @5
    @0
    @1
    @0
    cN
    cn0
    wcel
    @1
    cn
    wcel
    cK
    cN
    elfz3nn0
    cN
    faccl
    syl
    nncnd
    @0
    @3
    @0
    @2
    cn0
    wcel
    @3
    cn
    wcel
    cK
    cc0
    cN
    fznn0sub
    @2
    faccl
    syl
    #
    nncnd
    @0
    @5
    @0
    cK
    cn0
    wcel
    @5
    cn
    wcel
    cK
    cN
    elfznn0
    cK
    faccl
    syl
    #
    nncnd
    @0
    @3
    @7
    nnne0d
    @0
    @5
    @8
    nnne0d
    divdiv1d
    @0
    @6
    @4
    @5
    cdiv
    cN
    cK
    fallfacval4
    oveq1d
    cK
    cN
    bcval2
    3eqtr4rd
end
