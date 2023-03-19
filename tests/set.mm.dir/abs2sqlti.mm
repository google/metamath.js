include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "absge0i.mm"
include "abscli.mm"
include "lt2sqi.mm"
include "mp2an.mm"

theorem abs2sqlti
  let cA: class A
  let cB: class B
  assume abs2sqlti.1: |- A e. CC
  assume abs2sqlti.2: |- B e. CC


  assert |- ( ( abs ` A ) < ( abs ` B ) <-> ( ( abs ` A ) ^ 2 ) < ( ( abs ` B ) ^ 2 ) )

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
    clt
    wbr
    @0
    c2
    cexp
    co
    @1
    c2
    cexp
    co
    clt
    wbr
    wb
    cA
    abs2sqlti.1
    absge0i
    cB
    abs2sqlti.2
    absge0i
    @0
    @1
    cA
    abs2sqlti.1
    abscli
    cB
    abs2sqlti.2
    abscli
    lt2sqi
    mp2an
end
