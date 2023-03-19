include "cxdiv.mm"
include "co.mm"
include "cdiv.mm"
include "crp.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "rpred.mm"
include "rpne0d.mm"
include "rexdiv.mm"
include "syl3anc.mm"
include "rpdivcld.mm"
include "eqeltrd.mm"

theorem rpxdivcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpxdivcld.1: |- ( ph -> A e. RR+ )
  assume rpxdivcld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A /e B ) e. RR+ )

  proof
    wph
    cA
    cB
    cxdiv
    co
    #
    cA
    cB
    cdiv
    co
    #
    crp
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cB
    cc0
    wne
    @0
    @1
    wceq
    wph
    cA
    rpxdivcld.1
    rpred
    wph
    cB
    rpxdivcld.2
    rpred
    wph
    cB
    rpxdivcld.2
    rpne0d
    cA
    cB
    rexdiv
    syl3anc
    wph
    cA
    cB
    rpxdivcld.1
    rpxdivcld.2
    rpdivcld
    eqeltrd
end
