include "crp.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "relogmul.mm"
include "syl2anc.mm"

theorem relogmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume relogcld.1: |- ( ph -> A e. RR+ )
  assume relogmuld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) ) )

  proof
    wph
    cA
    crp
    wcel
    cB
    crp
    wcel
    cA
    cB
    cmul
    co
    clog
    cfv
    cA
    clog
    cfv
    cB
    clog
    cfv
    caddc
    co
    wceq
    relogcld.1
    relogmuld.2
    cA
    cB
    relogmul
    syl2anc
end
