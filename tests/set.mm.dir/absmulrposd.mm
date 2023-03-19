include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "recnd.mm"
include "absmuld.mm"
include "absidd.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem absmulrposd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume absmulrposd.1: |- ( ph -> 0 <_ A )
  assume absmulrposd.2: |- ( ph -> A e. RR )
  assume absmulrposd.3: |- ( ph -> B e. RR )


  assert |- ( ph -> ( abs ` ( A x. B ) ) = ( A x. ( abs ` B ) ) )

  proof
    wph
    cA
    cB
    cmul
    co
    cabs
    cfv
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    cmul
    co
    cA
    @1
    cmul
    co
    wph
    cA
    cB
    wph
    cA
    absmulrposd.2
    recnd
    wph
    cB
    absmulrposd.3
    recnd
    absmuld
    wph
    @0
    cA
    @1
    cmul
    wph
    cA
    absmulrposd.2
    absmulrposd.1
    absidd
    oveq1d
    eqtrd
end
