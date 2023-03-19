include "csymdif.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wn.mm"
include "df-br.mm"
include "elsymdif.mm"
include "bibi12i.mm"
include "xchbinxr.mm"
include "bitri.mm"

theorem brsymdif
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( A ( R /_\ S ) B <-> -. ( A R B <-> A S B ) )

  proof
    cA
    cB
    cR
    cS
    csymdif
    #
    wbr
    cA
    cB
    cop
    #
    @0
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cS
    wbr
    #
    wb
    #
    wn
    cA
    cB
    @0
    df-br
    @2
    @1
    cR
    wcel
    #
    @1
    cS
    wcel
    #
    wb
    @5
    @1
    cR
    cS
    elsymdif
    @3
    @6
    @4
    @7
    cA
    cB
    cR
    df-br
    cA
    cB
    cS
    df-br
    bibi12i
    xchbinxr
    bitri
end
