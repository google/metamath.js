include "cr.mm"
include "cxr.mm"
include "wss.mm"
include "ressxr.mm"
include "a1i.mm"
include "sstrd.mm"

theorem ssrexr
  let wph: wff ph
  let cA: class A
  assume ssrexr.1: |- ( ph -> A C_ RR )


  assert |- ( ph -> A C_ RR* )

  proof
    wph
    cA
    cr
    cxr
    ssrexr.1
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
end
