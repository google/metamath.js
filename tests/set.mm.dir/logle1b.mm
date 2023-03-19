include "crp.mm"
include "wcel.mm"
include "ceu.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "id.mm"
include "epr.mm"
include "a1i.mm"
include "logled.mm"
include "wceq.mm"
include "loge.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem logle1b
  let cA: class A


  assert |- ( A e. RR+ -> ( ( log ` A ) <_ 1 <-> A <_ _e ) )

  proof
    cA
    crp
    wcel
    #
    cA
    ceu
    cle
    wbr
    cA
    clog
    cfv
    #
    ceu
    clog
    cfv
    #
    cle
    wbr
    @1
    c1
    cle
    wbr
    @0
    cA
    ceu
    @0
    id
    ceu
    crp
    wcel
    @0
    epr
    a1i
    logled
    @0
    @2
    c1
    @1
    cle
    @2
    c1
    wceq
    @0
    loge
    a1i
    breq2d
    bitr2d
end
