include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cop.mm"
include "csn.mm"
include "wf.mm"
include "cword.mm"
include "cz.mm"
include "0zd.mm"
include "id.mm"
include "fsnd.mm"
include "fzo01.mm"
include "feq2i.mm"
include "sylibr.mm"
include "iswrdi.mm"
include "syl.mm"

theorem snopiswrd
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> { <. 0 , S >. } e. Word V )

  proof
    cS
    cV
    wcel
    #
    cc0
    c1
    cfzo
    co
    #
    cV
    cc0
    cS
    cop
    csn
    #
    wf
    #
    @2
    cV
    cword
    wcel
    @0
    cc0
    csn
    #
    cV
    @2
    wf
    @3
    @0
    cc0
    cS
    cz
    cV
    @0
    0zd
    @0
    id
    fsnd
    @1
    @4
    cV
    @2
    fzo01
    feq2i
    sylibr
    cV
    c1
    @2
    iswrdi
    syl
end
