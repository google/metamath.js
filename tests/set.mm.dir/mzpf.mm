include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cvv.mm"
include "wss.mm"
include "elfvex.mm"
include "cmzpcl.mm"
include "cint.mm"
include "mzpval.mm"
include "mzpclall.mm"
include "intss1.mm"
include "syl.mm"
include "eqsstrd.mm"
include "sselda.mm"
include "anidms.mm"
include "zex.mm"
include "ovex.mm"
include "elmap.mm"
include "sylib.mm"

theorem mzpf
  let cF: class F
  let cV: class V


  assert |- ( F e. ( mzPoly ` V ) -> F : ( ZZ ^m V ) --> ZZ )

  proof
    cF
    cV
    cmzp
    cfv
    #
    wcel
    #
    cF
    cz
    cz
    cV
    cmap
    co
    #
    cmap
    co
    #
    wcel
    #
    @2
    cz
    cF
    wf
    @1
    @4
    @1
    @0
    @3
    cF
    @1
    cV
    cvv
    wcel
    #
    @0
    @3
    wss
    cF
    cV
    cmzp
    elfvex
    @5
    @0
    cV
    cmzpcl
    cfv
    #
    cint
    #
    @3
    cV
    mzpval
    @5
    @3
    @6
    wcel
    @7
    @3
    wss
    cV
    mzpclall
    @3
    @6
    intss1
    syl
    eqsstrd
    syl
    sselda
    anidms
    cz
    @2
    cF
    zex
    cz
    cV
    cmap
    ovex
    elmap
    sylib
end
