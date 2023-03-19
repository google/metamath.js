include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "crp.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "nn0re.mm"
include "nnrp.mm"
include "fldivle.mm"
include "syl2an.mm"

theorem fldivnn0le
  let cK: class K
  let cL: class L


  assert |- ( ( K e. NN0 /\ L e. NN ) -> ( |_ ` ( K / L ) ) <_ ( K / L ) )

  proof
    cK
    cn0
    wcel
    cK
    cr
    wcel
    cL
    crp
    wcel
    cK
    cL
    cdiv
    co
    #
    cfl
    cfv
    @0
    cle
    wbr
    cL
    cn
    wcel
    cK
    nn0re
    cL
    nnrp
    cK
    cL
    fldivle
    syl2an
end
