include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "0red.mm"
include "ltsubaddd.mm"
include "recnd.mm"
include "addid2d.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem sublt0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume sublt0d.1: |- ( ph -> A e. RR )
  assume sublt0d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( ( A - B ) < 0 <-> A < B ) )

  proof
    wph
    cA
    cB
    cmin
    co
    cc0
    clt
    wbr
    cA
    cc0
    cB
    caddc
    co
    #
    clt
    wbr
    cA
    cB
    clt
    wbr
    wph
    cA
    cB
    cc0
    sublt0d.1
    sublt0d.2
    wph
    0red
    ltsubaddd
    wph
    @0
    cB
    cA
    clt
    wph
    cB
    wph
    cB
    sublt0d.2
    recnd
    addid2d
    breq2d
    bitrd
end
