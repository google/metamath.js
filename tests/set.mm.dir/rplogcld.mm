include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "crp.mm"
include "rplogcl.mm"
include "syl2anc.mm"

theorem rplogcld
  let wph: wff ph
  let cA: class A
  assume relogefd.1: |- ( ph -> A e. RR )
  assume rplogcld.2: |- ( ph -> 1 < A )


  assert |- ( ph -> ( log ` A ) e. RR+ )

  proof
    wph
    cA
    cr
    wcel
    c1
    cA
    clt
    wbr
    cA
    clog
    cfv
    crp
    wcel
    relogefd.1
    rplogcld.2
    cA
    rplogcl
    syl2anc
end
