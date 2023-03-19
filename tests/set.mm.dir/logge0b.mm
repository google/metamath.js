include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "cc0.mm"
include "1rp.mm"
include "a1i.mm"
include "id.mm"
include "logled.mm"
include "wceq.mm"
include "log1.mm"
include "breq1d.mm"
include "bitr2d.mm"

theorem logge0b
  let cA: class A


  assert |- ( A e. RR+ -> ( 0 <_ ( log ` A ) <-> 1 <_ A ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    cle
    wbr
    c1
    clog
    cfv
    #
    cA
    clog
    cfv
    #
    cle
    wbr
    cc0
    @2
    cle
    wbr
    @0
    c1
    cA
    c1
    crp
    wcel
    @0
    1rp
    a1i
    @0
    id
    logled
    @0
    @1
    cc0
    @2
    cle
    @1
    cc0
    wceq
    @0
    log1
    a1i
    breq1d
    bitr2d
end
