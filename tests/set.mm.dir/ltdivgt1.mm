include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "crp.mm"
include "wcel.mm"
include "1rp.mm"
include "a1i.mm"
include "ltdiv2d.mm"
include "rpcnd.mm"
include "div1d.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem ltdivgt1
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltdivgt1.1: |- ( ph -> A e. RR+ )
  assume ltdivgt1.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( 1 < B <-> ( A / B ) < A ) )

  proof
    wph
    c1
    cB
    clt
    wbr
    cA
    cB
    cdiv
    co
    #
    cA
    c1
    cdiv
    co
    #
    clt
    wbr
    @0
    cA
    clt
    wbr
    wph
    c1
    cB
    cA
    c1
    crp
    wcel
    wph
    1rp
    a1i
    ltdivgt1.2
    ltdivgt1.1
    ltdiv2d
    wph
    @1
    cA
    @0
    clt
    wph
    cA
    wph
    cA
    ltdivgt1.1
    rpcnd
    div1d
    breq2d
    bitrd
end
