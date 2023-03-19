include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "ch0o.mm"
include "ccom.mm"
include "cleo.mm"
include "cho.mm"
include "wbr.mm"
include "elpjhmop.mm"
include "leopsq.mm"
include "syl.mm"
include "elpjidm.mm"
include "breqtrd.mm"

theorem 0leopj
  let cT: class T


  assert |- ( T e. ran projh -> 0hop <_op T )

  proof
    cT
    cpjh
    crn
    wcel
    #
    ch0o
    cT
    cT
    ccom
    #
    cT
    cleo
    @0
    cT
    cho
    wcel
    ch0o
    @1
    cleo
    wbr
    cT
    elpjhmop
    cT
    leopsq
    syl
    cT
    elpjidm
    breqtrd
end
