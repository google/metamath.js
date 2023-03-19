include "cst.mm"
include "wcel.mm"
include "cch.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cr.mm"
include "sticl.mm"
include "unitssre.mm"
include "sseli.mm"
include "syl6.mm"

theorem stcl
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( S e. States -> ( A e. CH -> ( S ` A ) e. RR ) )

  proof
    cS
    cst
    wcel
    cA
    cch
    wcel
    cA
    cS
    cfv
    #
    cc0
    c1
    cicc
    co
    #
    wcel
    @0
    cr
    wcel
    cA
    cS
    sticl
    @1
    cr
    @0
    unitssre
    sseli
    syl6
end
