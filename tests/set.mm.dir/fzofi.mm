include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfzo.mm"
include "co.mm"
include "cfn.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wceq.mm"
include "fzoval.mm"
include "adantl.mm"
include "fzfi.mm"
include "syl6eqel.mm"
include "wn.mm"
include "c0.mm"
include "cxp.mm"
include "cpw.mm"
include "fzof.mm"
include "fdmi.mm"
include "ndmov.mm"
include "0fin.mm"
include "pm2.61i.mm"

theorem fzofi
  let cM: class M
  let cN: class N


  assert |- ( M ..^ N ) e. Fin

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    cfzo
    co
    #
    cfn
    wcel
    @2
    @3
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cfn
    @1
    @3
    @5
    wceq
    @0
    cM
    cN
    fzoval
    adantl
    cM
    @4
    fzfi
    syl6eqel
    @2
    wn
    @3
    c0
    cfn
    cM
    cN
    cz
    cfzo
    cz
    cz
    cxp
    cz
    cpw
    cfzo
    fzof
    fdmi
    ndmov
    0fin
    syl6eqel
    pm2.61i
end
