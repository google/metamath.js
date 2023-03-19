include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "absge0i.mm"
include "abscli.mm"
include "le2sqi.mm"
include "mp2an.mm"

theorem abs2sqlei
  let cA: class A
  let cB: class B
  assume abs2sqlei.1: |- A e. CC
  assume abs2sqlei.2: |- B e. CC


  assert |- ( ( abs ` A ) <_ ( abs ` B ) <-> ( ( abs ` A ) ^ 2 ) <_ ( ( abs ` B ) ^ 2 ) )

  proof
    cc0
    cA
    cabs
    cfv
    #
    cle
    wbr
    cc0
    cB
    cabs
    cfv
    #
    cle
    wbr
    @0
    @1
    cle
    wbr
    @0
    c2
    cexp
    co
    @1
    c2
    cexp
    co
    cle
    wbr
    wb
    cA
    abs2sqlei.1
    absge0i
    cB
    abs2sqlei.2
    absge0i
    @0
    @1
    cA
    abs2sqlei.1
    abscli
    cB
    abs2sqlei.2
    abscli
    le2sqi
    mp2an
end
