include "crp.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "relogdiv.mm"
include "syl2anc.mm"

theorem relogdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume relogcld.1: |- ( ph -> A e. RR+ )
  assume relogmuld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( log ` ( A / B ) ) = ( ( log ` A ) - ( log ` B ) ) )

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
    cdiv
    co
    clog
    cfv
    cA
    clog
    cfv
    cB
    clog
    cfv
    cmin
    co
    wceq
    relogcld.1
    relogmuld.2
    cA
    cB
    relogdiv
    syl2anc
end
