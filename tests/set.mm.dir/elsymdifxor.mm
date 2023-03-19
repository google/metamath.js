include "wcel.mm"
include "wb.mm"
include "wn.mm"
include "wxo.mm"
include "csymdif.mm"
include "xnor.mm"
include "notbii.mm"
include "elsymdif.mm"
include "notnotb.mm"
include "3bitr4i.mm"

theorem elsymdifxor
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B /_\ C ) <-> ( A e. B \/_ A e. C ) )

  proof
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wb
    #
    wn
    @0
    @1
    wxo
    #
    wn
    #
    wn
    cA
    cB
    cC
    csymdif
    wcel
    @3
    @2
    @4
    @0
    @1
    xnor
    notbii
    cA
    cB
    cC
    elsymdif
    @3
    notnotb
    3bitr4i
end
