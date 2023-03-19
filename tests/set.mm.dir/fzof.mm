include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cz.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cfzo.mm"
include "wf.mm"
include "wss.mm"
include "cuz.mm"
include "cfv.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "ovex.mm"
include "elpw.mm"
include "mpbir.mm"
include "rgen2w.mm"
include "df-fzo.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem fzof
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let cM: class M


  assert |- ..^ : ( ZZ X. ZZ ) --> ~P ZZ

  proof
    vm
    cv
    #
    vn
    cv
    c1
    cmin
    co
    #
    cfz
    co
    #
    cz
    cpw
    #
    wcel
    #
    vn
    cz
    wral
    vm
    cz
    wral
    cz
    cz
    cxp
    @3
    cfzo
    wf
    @4
    vm
    vn
    cz
    cz
    @4
    @2
    cz
    wss
    @2
    @0
    cuz
    cfv
    cz
    @0
    @1
    fzssuz
    @0
    uzssz
    sstri
    @2
    cz
    @0
    @1
    cfz
    ovex
    elpw
    mpbir
    rgen2w
    vm
    vn
    cz
    cz
    @2
    @3
    cfzo
    vm
    vn
    df-fzo
    fmpt2
    mpbi
end
